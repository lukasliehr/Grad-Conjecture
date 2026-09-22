import AKCY9ActualNewtonSmoothingDefect

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3500
open Set

namespace Grad.NashMoser.OriginalIteration
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.SmoothingFamily Grad.Q24Realization Grad.NashMoser.OriginalLimit Grad.NashMoser.Numeric

variable {parameters : PhaseParameters} {reference : Seed.Parameters}
    {inside : reference ∈ Seed.parameterDomain} {base loss : ℕ} {cellLength : ℝ}
    {neighborhood : OriginalNewtonNeighborhood parameters reference inside base}

theorem seminorm_unit_smul {E : Type*} [AddCommGroup E] [Module ℝ E]
    (size : Seminorm ℝ E) (value : E) (t : ℝ) (member : t ∈ Icc (0:ℝ) 1) :
    size (t•value) ≤ size value := by
  rw [map_smul_eq_mul,Real.norm_eq_abs,abs_of_nonneg member.1]
  exact mul_le_of_le_one_left (apply_nonneg size value) member.2

namespace OriginalNewtonInverse
variable (inverse : OriginalNewtonInverse neighborhood cellLength loss)

def quadraticConstant (lossLarge : 6 ≤ loss) : ℝ :=
  max 1 (neighborhood.taylorConstant cellLength loss lossLarge loss *
    ((1+2*inverse.correctionConstant (2*loss))*(inverse.correctionConstant 0)^2+
      2*inverse.correctionConstant (2*loss)*inverse.correctionConstant 0))

theorem quadraticConstant_one_le (lossLarge : 6 ≤ loss) :
    1 ≤ inverse.quadraticConstant lossLarge := le_max_left _ _

/-- NM07's actual nonlinear remainder on the already admissible next chord.
The proof uses QYP's second derivative, not a supplied Taylor estimate. -/
theorem quadraticRemainder_bound (lossLarge : 6 ≤ loss) (finite : OriginalFiniteParameter)
    (member : finite ∈ neighborhood.parameterDomain) (state : stateSmoothRange parameters reference inside)
    (low : stateSize parameters reference inside base loss state ≤ neighborhood.radius)
    (scale previous : ℝ) (scaleLarge : 1 ≤ scale) (previousLarge : 1 ≤ previous) (previousLe : previous ≤ scale)
    (coarse : ∀ grade, stateSize parameters reference inside base grade state ≤
      inverse.correctionConstant grade * previous ^ (grade:ℝ))
    (residualSmall : inverse.residualSize finite state ≤ 1)
    (chord : ∀ t ∈ Icc (0:ℝ) 1,
      stateSize parameters reference inside base 0 (state+t•inverse.correction finite state scale) ≤ 2*neighborhood.radius) :
    let lowBase : stateSize parameters reference inside base 0 state ≤ 2*neighborhood.radius :=
      ((stateSize_mono parameters reference inside base (Nat.zero_le loss) state).trans low).trans
        (by linarith [neighborhood.radiusPositive])
    sourceSize parameters base loss
      (originalLiteralTaylorRemainder parameters cellLength reference inside (finite.1,finite.2,state)
        (neighborhood.patchInside (neighborhood.seedInside finite member)) (neighborhood.axis state lowBase)
        (finite.1,finite.2,state+inverse.correction finite state scale)) ≤
    inverse.quadraticConstant lossLarge * scale ^ (2*(loss:ℝ)) * (inverse.residualSize finite state)^2 := by
  intro lowBase
  have positive : 0 < scale := lt_of_lt_of_le zero_lt_one scaleLarge
  let power := scale ^ ((2*loss:ℕ):ℝ)
  have powerOne : 1 ≤ power := Real.one_le_rpow scaleLarge (Nat.cast_nonneg _)
  have residualNonnegative : 0 ≤ inverse.residualSize finite state := apply_nonneg _ _
  have highNonnegative : 0 ≤ inverse.correctionConstant (2*loss) :=
    (by norm_num : (0:ℝ) ≤ 1).trans (inverse.correctionConstant_one_le _)
  have lowNonnegative : 0 ≤ inverse.correctionConstant 0 :=
    (by norm_num : (0:ℝ) ≤ 1).trans (inverse.correctionConstant_one_le _)
  have highStep := inverse.correction_bound finite member state low scale positive (2*loss)
  have lowStep := inverse.correction_bound finite member state low scale positive 0
  simp only [Nat.cast_zero,Real.rpow_zero,mul_one] at lowStep
  have stateHigh : stateSize parameters reference inside base (2*loss) state ≤
      inverse.correctionConstant (2*loss)*power :=
    (coarse (2*loss)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by linarith : 0 ≤ previous) previousLe (Nat.cast_nonneg _)) highNonnegative)
  have highStepCoarse : stateSize parameters reference inside base (2*loss)
      (inverse.correction finite state scale) ≤ inverse.correctionConstant (2*loss)*power := by
    apply highStep.trans
    simpa only [mul_one] using (mul_le_mul_of_nonneg_left residualSmall
      (mul_nonneg highNonnegative (by linarith : 0 ≤ power)))
  have segmentHigh (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      stateSize parameters reference inside base (2*loss) (state+t•inverse.correction finite state scale) ≤
      2*inverse.correctionConstant (2*loss)*power := by
    exact (map_add_le_add (stateSize parameters reference inside base (2*loss)) _ _).trans
      ((add_le_add stateHigh ((seminorm_unit_smul _ _ t ht).trans highStepCoarse)).trans_eq (by ring))
  have bound := neighborhood.taylor_bound cellLength loss lossLarge loss finite member state
    (inverse.correction finite state scale) lowBase (2*inverse.correctionConstant (2*loss)*power)
    (fun t ht => ⟨chord t ht,by simpa only [show loss+loss = 2*loss by omega] using segmentHigh t ht⟩)
  rw [show loss+loss = 2*loss by omega] at bound
  have square : (stateSize parameters reference inside base 0 (inverse.correction finite state scale))^2 ≤
      (inverse.correctionConstant 0*inverse.residualSize finite state)^2 := by
    nlinarith [apply_nonneg (stateSize parameters reference inside base 0) (inverse.correction finite state scale)]
  have highFactor : 1+2*inverse.correctionConstant (2*loss)*power ≤
      (1+2*inverse.correctionConstant (2*loss))*power := by nlinarith
  have first := mul_le_mul highFactor square (sq_nonneg _)
    (mul_nonneg (by linarith) (by linarith : 0 ≤ power))
  have second := mul_le_mul (mul_le_mul_of_nonneg_left highStep (by norm_num : (0:ℝ) ≤ 2))
    lowStep (apply_nonneg _ _) (by positivity)
  have paid := mul_le_mul_of_nonneg_left (add_le_add first second)
    (neighborhood.taylorConstant_nonnegative cellLength loss lossLarge loss)
  apply bound.trans (paid.trans ?_)
  have constantBound : neighborhood.taylorConstant cellLength loss lossLarge loss *
    ((1+2*inverse.correctionConstant (2*loss))*(inverse.correctionConstant 0)^2+
      2*inverse.correctionConstant (2*loss)*inverse.correctionConstant 0) ≤ inverse.quadraticConstant lossLarge := le_max_right _ _
  have final := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right constantBound (by linarith : 0 ≤ power))
      (sq_nonneg (inverse.residualSize finite state))
  change _ ≤ inverse.quadraticConstant lossLarge*scale^(2*(loss:ℝ))*(inverse.residualSize finite state)^2
  have exponent : ((2*loss:ℕ):ℝ) = 2*(loss:ℝ) := by push_cast; rfl
  dsimp only [power] at final ⊢
  rw [exponent] at final ⊢
  exact (le_of_eq (by ring)).trans final

end OriginalNewtonInverse
end Grad.NashMoser.OriginalIteration
