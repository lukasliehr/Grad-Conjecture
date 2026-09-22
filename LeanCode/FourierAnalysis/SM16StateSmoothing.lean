import SM15StateCarrier

noncomputable section

namespace Grad.SmoothingFamily

open Grad.ClosedJets Grad.CartesianState Grad.COR12Extension

def stateSmoothing (parameters : PhaseParameters) (scale : ℝ) : StateCore parameters →ₗ[ℂ] StateCore parameters :=
  (axisSmoothing parameters.sigma0 scale).prodMap
    ((ambientSmoothing parameters scale).prodMap (ambientSmoothing parameters scale))

def stateScaleDerivative (parameters : PhaseParameters) (order : ℕ) (scale : ℝ) :
    StateCore parameters →ₗ[ℂ] StateCore parameters :=
  (axisScaleDerivative parameters.sigma0 order scale).prodMap
    ((ambientScaleDerivative parameters order scale).prodMap (ambientScaleDerivative parameters order scale))

theorem stateScaleDerivative_zero (parameters : PhaseParameters) (scale : ℝ) :
    stateScaleDerivative parameters 0 scale = stateSmoothing parameters scale := by
  simp only [stateScaleDerivative, stateSmoothing, axisScaleDerivative_zero, ambientScaleDerivative_zero]

theorem three_component_bound (a b c x y z first second power : ℝ)
    (xNonnegative : 0 ≤ x) (yNonnegative : 0 ≤ y) (zNonnegative : 0 ≤ z) (powerNonnegative : 0 ≤ power)
    (aBound : a ≤ first * power * x) (bBound : b ≤ second * power * y) (cBound : c ≤ second * power * z) :
    a + b + c ≤ max first second * power * (x + y + z) := by
  calc
    _ ≤ first * power * x + second * power * y + second * power * z := add_le_add (add_le_add aBound bBound) cBound
    _ ≤ max first second * power * x + max first second * power * y + max first second * power * z := by
      gcongr
      · exact le_max_left _ _
      · exact le_max_right _ _
      · exact le_max_right _ _
    _ = _ := by ring

def stateSmoothingConstant (lower upper : ℕ) : ℝ :=
  max ((2 : ℝ) ^ (upper - lower))
    (sameGradeConstant upper * sameGradeConstant lower * (2 : ℝ) ^ (upper - lower))

def stateRemainderConstant (lower upper : ℕ) : ℝ :=
  max 1 (sameGradeConstant lower * sameGradeConstant upper)

def stateDerivativeConstant (lower upper order : ℕ) : ℝ :=
  max ((2 : ℝ) ^ (upper + 1) * profileBound order)
    (sameGradeConstant upper * sameGradeConstant lower * (2 : ℝ) ^ upper * profileBound order)

theorem stateSmoothing_norm_le (parameters : PhaseParameters) (scale : ℝ) (positive : 0 < scale)
    (lower upper : ℕ) (ordered : lower ≤ upper) (state : StateCore parameters) :
    ‖stateToGrade parameters upper (stateSmoothing parameters scale state)‖ ≤
      stateSmoothingConstant lower upper * scale ^ (upper - lower) * ‖stateToGrade parameters lower state‖ := by
  rw [stateToGrade_norm, stateToGrade_norm]
  apply three_component_bound _ _ _ _ _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (by positivity)
  · change ‖axisToGrade parameters.sigma0 (upper + 1) (axisSmoothing parameters.sigma0 scale state.1)‖ ≤ _
    simpa only [mul_pow, mul_assoc] using
      shifted_axisSmoothing_norm_le parameters.sigma0 scale positive lower upper 1 ordered state.1
  · exact ambientSmoothing_norm_le parameters scale positive lower upper ordered state.2.1
  · exact ambientSmoothing_norm_le parameters scale positive lower upper ordered state.2.2

theorem stateRemainder_norm_le (parameters : PhaseParameters) (scale : ℝ) (positive : 0 < scale)
    (lower upper : ℕ) (ordered : lower ≤ upper) (state : StateCore parameters) :
    ‖stateToGrade parameters lower (state - stateSmoothing parameters scale state)‖ ≤
      stateRemainderConstant lower upper * scale ^ ((lower : ℝ) - (upper : ℝ)) *
        ‖stateToGrade parameters upper state‖ := by
  rw [stateToGrade_norm, stateToGrade_norm]
  apply three_component_bound _ _ _ _ _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (Real.rpow_nonneg positive.le _)
  · change ‖axisToGrade parameters.sigma0 (lower + 1) (state.1 - axisSmoothing parameters.sigma0 scale state.1)‖ ≤ _
    have axisBound := axisRemainder_norm_le parameters.sigma0 scale positive (lower + 1) (upper + 1)
      (Nat.add_le_add_right ordered 1) state.1
    have exponent : ((lower + 1 : ℕ) : ℝ) - ((upper + 1 : ℕ) : ℝ) = (lower : ℝ) - (upper : ℝ) := by push_cast; ring
    simpa only [exponent, one_mul] using axisBound
  · exact ambientRemainder_norm_le parameters scale positive lower upper ordered state.2.1
  · exact ambientRemainder_norm_le parameters scale positive lower upper ordered state.2.2

theorem stateScaleDerivative_norm_le (parameters : PhaseParameters) (scale : ℝ) (positive : 0 < scale)
    (lower upper order : ℕ) (positiveOrder : 0 < order) (state : StateCore parameters) :
    ‖stateToGrade parameters upper (stateScaleDerivative parameters order scale state)‖ ≤
      stateDerivativeConstant lower upper order * scale ^ ((upper : ℝ) - (lower : ℝ) - (order : ℝ)) *
        ‖stateToGrade parameters lower state‖ := by
  rw [stateToGrade_norm, stateToGrade_norm]
  apply three_component_bound _ _ _ _ _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (Real.rpow_nonneg positive.le _)
  · change ‖axisToGrade parameters.sigma0 (upper + 1) (axisScaleDerivative parameters.sigma0 order scale state.1)‖ ≤ _
    have axisBound := axisScaleDerivative_norm_le parameters.sigma0 scale positive (lower + 1) (upper + 1)
      order positiveOrder state.1
    have exponent : ((upper + 1 : ℕ) : ℝ) - ((lower + 1 : ℕ) : ℝ) - (order : ℝ) =
        (upper : ℝ) - (lower : ℝ) - (order : ℝ) := by push_cast; ring
    simpa only [exponent] using axisBound
  · exact ambientScaleDerivative_norm_le parameters scale positive lower upper order positiveOrder state.2.1
  · exact ambientScaleDerivative_norm_le parameters scale positive lower upper order positiveOrder state.2.2

def StateReality {parameters : PhaseParameters} (state : StateCore parameters) : Prop :=
  AxisReality state.1 ∧ cartesianCoreConjugation parameters state.2.1 = state.2.1 ∧
    cartesianCoreConjugation parameters state.2.2 = state.2.2

theorem stateScaleDerivative_reality (parameters : PhaseParameters) (order : ℕ) (scale : ℝ)
    (state : StateCore parameters) (real : StateReality state) :
    StateReality (stateScaleDerivative parameters order scale state) :=
  ⟨axisScaleDerivative_reality parameters.sigma0 order scale state.1 real.1,
    ambientScaleDerivative_reality parameters order scale state.2.1 real.2.1,
    ambientScaleDerivative_reality parameters order scale state.2.2 real.2.2⟩

theorem stateSmoothing_reality (parameters : PhaseParameters) (scale : ℝ)
    (state : StateCore parameters) (real : StateReality state) : StateReality (stateSmoothing parameters scale state) := by
  rw [← stateScaleDerivative_zero]
  exact stateScaleDerivative_reality parameters 0 scale state real

end Grad.SmoothingFamily
