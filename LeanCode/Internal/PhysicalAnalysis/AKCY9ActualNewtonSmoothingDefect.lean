import AKCY8ActualNewtonCorrectionEstimates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3500

namespace Grad.NashMoser.OriginalIteration
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.SmoothingFamily Grad.Q24Realization Grad.NashMoser.OriginalLimit Grad.NashMoser.Numeric
open Grad.PhysicalCoordinates

variable {parameters : PhaseParameters} {reference : Seed.Parameters}
    {inside : reference ∈ Seed.parameterDomain} {base loss : ℕ} {cellLength : ℝ}
    {neighborhood : OriginalNewtonNeighborhood parameters reference inside base}

namespace OriginalNewtonInverse
variable (inverse : OriginalNewtonInverse neighborhood cellLength loss)

def smoothingDefect (finite : OriginalFiniteParameter) (state : stateSmoothRange parameters reference inside)
    (scale : ℝ) : stateSmoothRange parameters reference inside :=
  inverse.map finite state (inverse.residual finite state)-
    originalStateSmoothing parameters reference inside scale (inverse.map finite state (inverse.residual finite state))

def tailConstant (_inverse : OriginalNewtonInverse neighborhood cellLength loss) (grade cutoff : ℕ) : ℝ :=
  originalSmoothingTail parameters reference inside (base+grade) (base+(grade+cutoff))

theorem tailConstant_nonnegative (grade cutoff : ℕ) : 0 ≤ inverse.tailConstant grade cutoff := by
  unfold tailConstant originalSmoothingTail stateRemainderConstant
  exact mul_nonneg (originalProjectionConstant_nonnegative parameters reference inside (base+grade))
    (zero_le_one.trans (le_max_left _ _))

theorem smoothingDefect_bound (lossLarge : 6 ≤ loss) (finite : OriginalFiniteParameter)
    (member : finite ∈ neighborhood.parameterDomain) (state : stateSmoothRange parameters reference inside)
    (low : stateSize parameters reference inside base loss state ≤ neighborhood.radius)
    (scale previous : ℝ) (positive : 0 < scale) (previousLarge : 1 ≤ previous)
    (coarse : ∀ grade, stateSize parameters reference inside base grade state ≤
      inverse.correctionConstant grade * previous ^ (grade:ℝ))
    (residualSmall : inverse.residualSize finite state ≤ 1) (grade cutoff : ℕ) :
    stateSize parameters reference inside base grade (inverse.smoothingDefect finite state scale) ≤
      inverse.tailConstant grade cutoff * inverse.coarseInverseConstant lossLarge (grade+cutoff) *
        scale ^ (-(cutoff:ℝ)) * previous ^ ((grade+cutoff+2*loss:ℕ):ℝ) := by
  have bound := originalStateRemainder_norm_le parameters reference inside scale positive
    (base+grade) (base+(grade+cutoff)) (by omega) (by have := neighborhood.baseLarge; omega)
    (inverse.map finite state (inverse.residual finite state))
  have exponent : ((base+grade:ℕ):ℝ)-((base+(grade+cutoff):ℕ):ℝ) = -(cutoff:ℝ) := by push_cast; ring
  rw [exponent] at bound
  have high := inverse.coarse_inverse_bound lossLarge finite member state low previous previousLarge coarse residualSmall (grade+cutoff)
  have paid := mul_le_mul_of_nonneg_left high
    (mul_nonneg (inverse.tailConstant_nonnegative grade cutoff) (Real.rpow_nonneg positive.le (-(cutoff:ℝ))))
  exact bound.trans (paid.trans_eq (by ring))

def defectConstant (lossLarge : 6 ≤ loss) (cutoff : ℕ) : ℝ :=
  max 1 (neighborhood.forwardConstant cellLength loss lossLarge loss *
    ((1+inverse.correctionConstant (2*loss)) * inverse.tailConstant 0 cutoff *
      inverse.coarseInverseConstant lossLarge cutoff +
      inverse.tailConstant (2*loss) cutoff * inverse.coarseInverseConstant lossLarge (2*loss+cutoff)))

theorem defectConstant_one_le (lossLarge : 6 ≤ loss) (cutoff : ℕ) :
    1 ≤ inverse.defectConstant lossLarge cutoff := le_max_left _ _

/-- The exact linearized smoothing defect at residual grade d, using only
the already established finite stage high bounds. -/
theorem forward_smoothingDefect_bound (lossLarge : 6 ≤ loss) (finite : OriginalFiniteParameter)
    (member : finite ∈ neighborhood.parameterDomain) (state : stateSmoothRange parameters reference inside)
    (low : stateSize parameters reference inside base loss state ≤ neighborhood.radius)
    (scale previous : ℝ) (positive : 0 < scale) (previousLarge : 1 ≤ previous)
    (coarse : ∀ grade, stateSize parameters reference inside base grade state ≤
      inverse.correctionConstant grade * previous ^ (grade:ℝ))
    (residualSmall : inverse.residualSize finite state ≤ 1) (cutoff : ℕ) :
    let lowBase : stateSize parameters reference inside base 0 state ≤ 2*neighborhood.radius :=
      ((stateSize_mono parameters reference inside base (Nat.zero_le loss) state).trans low).trans
        (by linarith [neighborhood.radiusPositive])
    sourceSize parameters base loss
      (literalPhysicalSmoothForward parameters cellLength reference inside finite.1
        (neighborhood.patchInside (neighborhood.seedInside finite member)) (finite.2,state)
        (neighborhood.axis state lowBase) (inverse.smoothingDefect finite state scale)) ≤
    inverse.defectConstant lossLarge cutoff * scale ^ (-(cutoff:ℝ)) * previous ^ ((cutoff+4*loss:ℕ):ℝ) := by
  intro lowBase
  have bound := neighborhood.forward_bound cellLength loss lossLarge loss finite member state lowBase
    (inverse.smoothingDefect finite state scale)
  have double : loss+loss = 2*loss := by omega
  rw [double] at bound
  have lowDefect := inverse.smoothingDefect_bound lossLarge finite member state low scale previous positive
    previousLarge coarse residualSmall 0 cutoff
  simp only [zero_add] at lowDefect
  have highDefect := inverse.smoothingDefect_bound lossLarge finite member state low scale previous positive
    previousLarge coarse residualSmall (2*loss) cutoff
  have highIndex : 2*loss+cutoff+2*loss = cutoff+4*loss := by omega
  rw [highIndex] at highDefect
  have powerOne : 1 ≤ previous ^ ((2*loss:ℕ):ℝ) := Real.one_le_rpow previousLarge (Nat.cast_nonneg _)
  have stateBound : 1+stateSize parameters reference inside base (2*loss) state ≤
      (1+inverse.correctionConstant (2*loss))*previous ^ ((2*loss:ℕ):ℝ) := by
    have high := coarse (2*loss)
    nlinarith
  have first := mul_le_mul stateBound lowDefect (apply_nonneg _ _)
    (mul_nonneg (by have := inverse.correctionConstant_one_le (2*loss); linarith) (by linarith))
  have powers : previous ^ ((2*loss:ℕ):ℝ) * previous ^ ((cutoff+2*loss:ℕ):ℝ) =
      previous ^ ((cutoff+4*loss:ℕ):ℝ) := by
    rw [← Real.rpow_add (by linarith : 0 < previous)]
    congr 1
    push_cast
    ring
  have firstPaid : (1+stateSize parameters reference inside base (2*loss) state) *
      stateSize parameters reference inside base 0 (inverse.smoothingDefect finite state scale) ≤
      ((1+inverse.correctionConstant (2*loss))*inverse.tailConstant 0 cutoff*
        inverse.coarseInverseConstant lossLarge cutoff)*scale ^ (-(cutoff:ℝ))*previous ^ ((cutoff+4*loss:ℕ):ℝ) := by
    apply first.trans_eq
    calc
      _ = ((1+inverse.correctionConstant (2*loss))*inverse.tailConstant 0 cutoff*
        inverse.coarseInverseConstant lossLarge cutoff)*scale ^ (-(cutoff:ℝ))*
          (previous ^ ((2*loss:ℕ):ℝ)*previous ^ ((cutoff+2*loss:ℕ):ℝ)) := by ring
      _ = _ := by rw [powers]
  have paid := mul_le_mul_of_nonneg_left (add_le_add firstPaid highDefect)
    (neighborhood.forwardConstant_nonnegative cellLength loss lossLarge loss)
  apply bound.trans (paid.trans ?_)
  have constantBound : neighborhood.forwardConstant cellLength loss lossLarge loss *
    ((1+inverse.correctionConstant (2*loss))*inverse.tailConstant 0 cutoff*
      inverse.coarseInverseConstant lossLarge cutoff +
      inverse.tailConstant (2*loss) cutoff*inverse.coarseInverseConstant lossLarge (2*loss+cutoff)) ≤
      inverse.defectConstant lossLarge cutoff := le_max_right _ _
  have final := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right constantBound (Real.rpow_nonneg positive.le (-(cutoff:ℝ))))
    (Real.rpow_nonneg (by linarith : 0 ≤ previous) ((cutoff+4*loss:ℕ):ℝ))
  exact (le_of_eq (by ring)).trans final

end OriginalNewtonInverse

theorem smoothingDefect_power (initial : ℝ) (positive : 0 < initial) (index cutoff loss : ℕ) :
    newtonTime initial index ^ (-(cutoff:ℝ))*previousStageTime initial index ^ ((cutoff+4*loss:ℕ):ℝ) =
    newtonTime initial index ^ (-(((cutoff:ℝ)-8*loss)/3)) := by
  rw [previousStageTime,← Real.rpow_mul (newtonTime_pos positive index).le,
    ← Real.rpow_add (newtonTime_pos positive index)]
  congr 1
  push_cast
  ring

end Grad.NashMoser.OriginalIteration
