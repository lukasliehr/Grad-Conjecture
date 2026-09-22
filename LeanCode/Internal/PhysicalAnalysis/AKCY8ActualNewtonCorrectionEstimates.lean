import AKCY7FiniteStageHighBudgets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3500

namespace Grad.NashMoser.OriginalIteration
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.SmoothingFamily Grad.Q24Realization Grad.NashMoser.OriginalLimit Grad.NashMoser.Numeric

variable {parameters : PhaseParameters} {reference : Seed.Parameters}
    {inside : reference ∈ Seed.parameterDomain} {base loss : ℕ} {cellLength : ℝ}
    {neighborhood : OriginalNewtonNeighborhood parameters reference inside base}

namespace OriginalNewtonInverse
variable (inverse : OriginalNewtonInverse neighborhood cellLength loss)

def residual (_inverse : OriginalNewtonInverse neighborhood cellLength loss) (finite : OriginalFiniteParameter) (state : stateSmoothRange parameters reference inside) :
    sourceSmoothRange parameters := originalNonlinearSource parameters cellLength reference inside finite state

def residualSize (finite : OriginalFiniteParameter) (state : stateSmoothRange parameters reference inside) : ℝ :=
  sourceSize parameters base loss (inverse.residual finite state)

def correction (finite : OriginalFiniteParameter) (state : stateSmoothRange parameters reference inside)
    (scale : ℝ) : stateSmoothRange parameters reference inside :=
  smoothedNewtonCorrection parameters reference inside scale (inverse.map finite state) (inverse.residual finite state)

def correctionConstant (grade : ℕ) : ℝ :=
  max 1 (originalSmoothingGain parameters reference inside base (base+grade) *
    inverse.constant 0 * (2+neighborhood.radius))

theorem correctionConstant_one_le (grade : ℕ) : 1 ≤ inverse.correctionConstant grade := le_max_left _ _

theorem inverse_low_bound (finite : OriginalFiniteParameter) (member : finite ∈ neighborhood.parameterDomain)
    (state : stateSmoothRange parameters reference inside)
    (low : stateSize parameters reference inside base loss state ≤ neighborhood.radius) :
    stateSize parameters reference inside base 0 (inverse.map finite state (inverse.residual finite state)) ≤
      inverse.constant 0 * (2+neighborhood.radius) * inverse.residualSize finite state := by
  have lowBase := (stateSize_mono parameters reference inside base (Nat.zero_le loss) state).trans low
  have bound := inverse.bounded 0 finite member state
    (lowBase.trans (by linarith [neighborhood.radiusPositive])) (inverse.residual finite state)
  simp only [zero_add] at bound
  apply bound.trans
  have residualNonnegative : 0 ≤ inverse.residualSize finite state := apply_nonneg _ _
  have paid := mul_le_mul_of_nonneg_right (add_le_add (le_refl (1:ℝ)) low) residualNonnegative
  have result := mul_le_mul_of_nonneg_left (add_le_add (le_refl (inverse.residualSize finite state)) paid) (inverse.nonnegative 0)
  change inverse.constant 0 * (inverse.residualSize finite state+
    (1+stateSize parameters reference inside base loss state)*inverse.residualSize finite state) ≤ _
  exact result.trans_eq (by ring)

theorem correction_bound (finite : OriginalFiniteParameter) (member : finite ∈ neighborhood.parameterDomain)
    (state : stateSmoothRange parameters reference inside)
    (low : stateSize parameters reference inside base loss state ≤ neighborhood.radius)
    (scale : ℝ) (positive : 0 < scale) (grade : ℕ) :
    stateSize parameters reference inside base grade (inverse.correction finite state scale) ≤
      inverse.correctionConstant grade * scale ^ (grade:ℝ) * inverse.residualSize finite state := by
  have gainNonnegative : 0 ≤ originalSmoothingGain parameters reference inside base (base+grade) := by
    unfold originalSmoothingGain
    exact mul_nonneg (originalProjectionConstant_nonnegative parameters reference inside (base+grade))
      ((pow_nonneg (by norm_num : (0:ℝ) ≤ 2) _).trans (le_max_left _ _))
  have smoothBound := smoothedNewtonCorrection_norm_le parameters reference inside base grade
    (by have := neighborhood.baseLarge; omega) scale positive (inverse.map finite state) (inverse.residual finite state)
  rw [← Real.rpow_natCast] at smoothBound
  have paid := mul_le_mul_of_nonneg_left (inverse.inverse_low_bound finite member state low)
    (mul_nonneg gainNonnegative (Real.rpow_nonneg positive.le (grade:ℝ)))
  apply smoothBound.trans (paid.trans ?_)
  have constantBound : originalSmoothingGain parameters reference inside base (base+grade)*inverse.constant 0*
      (2+neighborhood.radius) ≤ inverse.correctionConstant grade := le_max_right _ _
  have final := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right constantBound (Real.rpow_nonneg positive.le (grade:ℝ)))
      (apply_nonneg (sourceSize parameters base loss) (inverse.residual finite state))
  exact le_trans (by ring_nf; rfl) final

/-- The unsmoothed Newton solution has the written coarse high estimate;
only the finite stage's high budgets and its residual <=1 enter. -/
def coarseInverseConstant (lossLarge : 6 ≤ loss) (grade : ℕ) : ℝ :=
  max 1 (inverse.constant grade *
    (neighborhood.residualConstant cellLength loss lossLarge (grade+loss) *
      (1+inverse.correctionConstant (grade+2*loss)) + 1+inverse.correctionConstant (grade+loss)))

theorem coarseInverseConstant_one_le (lossLarge : 6 ≤ loss) (grade : ℕ) :
    1 ≤ inverse.coarseInverseConstant lossLarge grade := le_max_left _ _

theorem coarse_inverse_bound (lossLarge : 6 ≤ loss) (finite : OriginalFiniteParameter)
    (member : finite ∈ neighborhood.parameterDomain) (state : stateSmoothRange parameters reference inside)
    (low : stateSize parameters reference inside base loss state ≤ neighborhood.radius)
    (previous : ℝ) (previousLarge : 1 ≤ previous)
    (coarse : ∀ grade, stateSize parameters reference inside base grade state ≤
      inverse.correctionConstant grade * previous ^ (grade:ℝ))
    (residualSmall : inverse.residualSize finite state ≤ 1) (grade : ℕ) :
    stateSize parameters reference inside base grade (inverse.map finite state (inverse.residual finite state)) ≤
      inverse.coarseInverseConstant lossLarge grade * previous ^ ((grade+2*loss:ℕ):ℝ) := by
  have lowBase := (stateSize_mono parameters reference inside base (Nat.zero_le loss) state).trans low
  have lowProduct : stateSize parameters reference inside base 0 state ≤ 2*neighborhood.radius :=
    lowBase.trans (by linarith [neighborhood.radiusPositive])
  have bound := inverse.bounded grade finite member state lowProduct (inverse.residual finite state)
  have residualBound := neighborhood.residual_bound cellLength loss lossLarge (grade+loss) finite member state lowProduct
  have gradeEq : grade+loss+loss = grade+2*loss := by omega
  rw [gradeEq] at residualBound
  let power := previous ^ ((grade+2*loss:ℕ):ℝ)
  have powerOne : 1 ≤ power := Real.one_le_rpow previousLarge (Nat.cast_nonneg _)
  have lowerPower : previous ^ ((grade+loss:ℕ):ℝ) ≤ power :=
    Real.rpow_le_rpow_of_exponent_le previousLarge (by exact_mod_cast (show grade+loss ≤ grade+2*loss by omega))
  have highState : 1+stateSize parameters reference inside base (grade+2*loss) state ≤
      (1+inverse.correctionConstant (grade+2*loss))*power := by
    have boundState := coarse (grade+2*loss)
    change stateSize parameters reference inside base (grade+2*loss) state ≤
      inverse.correctionConstant (grade+2*loss)*power at boundState
    nlinarith
  have lowerState : 1+stateSize parameters reference inside base (grade+loss) state ≤
      (1+inverse.correctionConstant (grade+loss))*power := by
    have boundState := (coarse (grade+loss)).trans (mul_le_mul_of_nonneg_left lowerPower
      ((by norm_num : (0:ℝ) ≤ 1).trans (inverse.correctionConstant_one_le (grade+loss))))
    nlinarith
  have residualHigh := residualBound.trans (mul_le_mul_of_nonneg_left highState
    (neighborhood.residualConstant_nonnegative cellLength loss lossLarge (grade+loss)))
  have residualLow := mul_le_mul lowerState residualSmall (apply_nonneg _ _)
    (mul_nonneg (by have := inverse.correctionConstant_one_le (grade+loss); linarith) (by linarith))
  have paid := mul_le_mul_of_nonneg_left (add_le_add residualHigh residualLow) (inverse.nonnegative grade)
  apply bound.trans (paid.trans ?_)
  have constantBound : inverse.constant grade *
      (neighborhood.residualConstant cellLength loss lossLarge (grade+loss) *
        (1+inverse.correctionConstant (grade+2*loss))+1+inverse.correctionConstant (grade+loss)) ≤
      inverse.coarseInverseConstant lossLarge grade := le_max_right _ _
  calc
    _ = (inverse.constant grade *
      (neighborhood.residualConstant cellLength loss lossLarge (grade+loss) *
        (1+inverse.correctionConstant (grade+2*loss))+1+inverse.correctionConstant (grade+loss)))*power := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right constantBound (by linarith)

end OriginalNewtonInverse
end Grad.NashMoser.OriginalIteration
