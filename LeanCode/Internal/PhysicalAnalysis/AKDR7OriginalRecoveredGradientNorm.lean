import AKDR6OriginalCovariantPrimitiveNorm
import AKBG10SameWeakGradientRecovery

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.CartesianStartup Grad.Constraints
open Grad.NonlinearProduct Grad.NonlinearQuotientBounds

def originalRecoveredGradientCore (parameters : PhaseParameters)
    (vector right : ACore parameters 2) : ACore parameters 2 :=
  vector - originalEquivariantAverageCore parameters vector +
    originalCovariantPrimitiveCore parameters
      (right + (2 : ℂ) • valueMapCore parameters quarterValueMap vector)

def originalRecoveredGradientConstant (grade : ℕ) : ℝ :=
  1 + originalAverageConstant grade + 2*originalCovariantPrimitiveConstant grade*‖quarterValueMap‖

theorem originalRecoveredGradientConstant_nonnegative (grade : ℕ) :
    0 ≤ originalRecoveredGradientConstant grade := by
  unfold originalRecoveredGradientConstant
  exact add_nonneg (add_nonneg zero_le_one (originalAverageConstant_nonnegative _))
    (mul_nonneg (mul_nonneg (by norm_num) (originalCovariantPrimitiveConstant_nonnegative _)) (norm_nonneg _))

/-- No derivative or high coefficient is multiplied into the unknown. This
is the actual order-zero gradient recovery used for the retained scalar. -/
theorem originalRecoveredGradientCore_bound (parameters : PhaseParameters)
    (vector right : ACore parameters 2) (grade : ℕ) :
    originalGradeNorm grade (originalRecoveredGradientCore parameters vector right) ≤
      originalRecoveredGradientConstant grade * originalGradeNorm grade vector +
        originalCovariantPrimitiveConstant grade * originalGradeNorm grade right := by
  have first := (originalGradeNorm_sub_le grade vector _).trans
    (add_le_add (le_refl _) (originalEquivariantAverageCore_bound parameters vector grade))
  have quarter : originalGradeNorm grade ((2 : ℂ) • valueMapCore parameters quarterValueMap vector) ≤
      2*‖quarterValueMap‖*originalGradeNorm grade vector := by
    rw [originalGradeNorm_smul]
    norm_num only [Complex.norm_ofNat]
    exact (mul_le_mul_of_nonneg_left (valueMapCore_bound quarterValueMap vector grade)
      (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (mul_assoc _ _ _).symm
  have input := (originalGradeNorm_add_le grade right _).trans (add_le_add (le_refl _) quarter)
  have primitive := (originalCovariantPrimitiveCore_bound parameters _ grade).trans
    (mul_le_mul_of_nonneg_left input (originalCovariantPrimitiveConstant_nonnegative _))
  exact (originalGradeNorm_add_le grade _ _).trans
    ((add_le_add first primitive).trans_eq (by unfold originalRecoveredGradientConstant; ring))

theorem originalRecoveredGradientCore_sameField (parameters : PhaseParameters)
    (vector right : ACore parameters 2) :
    originalSourceFieldLinear parameters (originalRecoveredGradientCore parameters vector right) =
      startupRecoveredGradient (originalSourceFieldLinear parameters vector)
        (originalSourceFieldLinear parameters right) := by
  rw [originalRecoveredGradientCore,map_add,map_sub,originalEquivariantAverageCore_sameField,
    originalCovariantPrimitiveCore_sameField,map_add,map_smul,originalSourceFieldLinear_valueMap]
  rfl

end Grad.OriginalCoreRealization
