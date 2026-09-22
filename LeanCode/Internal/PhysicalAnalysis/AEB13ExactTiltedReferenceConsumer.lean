import AEB12BoundedComplexTiltedInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Grad.AnnularTiltedReference
open Grad.CartesianState Grad.AnnularVariational Grad.AnnularGrades Grad.CircularHighWeak

section Consumer
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (collar : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

/-- The constructed complex-linear reference inverse, its exact weak form,
actual incoming trace and literal b-weighted energy bound on normalized data. -/
theorem actualBWeightedTiltedReference_consumer (data : AnnularForcing lower × AnnularBoundary) :
    let field := annularTiltVariationalInverse parameters lower length positive collar lengthPositive widthHalf widthLength data
    annularEnergyTrace lower length positive collar lengthPositive 0 field = data.2 ∧
    (∀ test : annularInnerZero lower length positive collar lengthPositive,
      annularTiltFormValue parameters lower length positive lengthPositive widthHalf widthLength field test.val =
        annularTiltFunctionalValue parameters lower length positive collar lengthPositive widthHalf widthLength data.1 test.val) ∧
    (∑' mode : HighAnnularMode, (highMultiplier mode.val.1)⁻¹ *
      ‖(bEnergyDecode lower length positive field).val mode‖ ^ 2) ≤
        annularTiltInverseConstant lower length ^ 2 * ‖data‖ ^ 2 := by
  dsimp only
  refine ⟨annularTiltVariationalSolution_inner parameters lower length positive collar lengthPositive widthHalf widthLength data.1 data.2,
    annularTiltVariationalSolution_weak parameters lower length positive collar lengthPositive widthHalf widthLength data.1 data.2, ?_⟩
  rw [← bEnergyDecode_norm_sq]
  have bound := pow_le_pow_left₀ (norm_nonneg _)
    (annularTiltVariationalLinear_bound parameters lower length positive collar lengthPositive widthHalf widthLength data) 2
  change ‖annularTiltVariationalLinear parameters lower length positive collar lengthPositive widthHalf widthLength data‖ ^ 2 ≤ _
  simpa only [mul_pow] using bound

/-- Uniqueness concerns the same constructed solution and complete zero-trace
test space, not a preselected inverse or a restricted family of test functions. -/
theorem actualBWeightedTiltedReference_unique (data : AnnularForcing lower × AnnularBoundary)
    (candidate : annularEnergySpace lower length positive)
    (innerLaw : annularEnergyTrace lower length positive collar lengthPositive 0 candidate = data.2)
    (weakLaw : ∀ test : annularInnerZero lower length positive collar lengthPositive,
      annularTiltFormValue parameters lower length positive lengthPositive widthHalf widthLength candidate test.val =
        annularTiltFunctionalValue parameters lower length positive collar lengthPositive widthHalf widthLength data.1 test.val) :
    candidate = annularTiltVariationalInverse parameters lower length positive collar lengthPositive widthHalf widthLength data :=
  annularTiltVariationalSolution_unique parameters lower length positive collar lengthPositive widthHalf widthLength
    data.1 data.2 candidate innerLaw weakLaw

/-- The decoded physical scalar has the original sharp incoming trace,
with precisely the fixed sqrt(b_m) normalization and no change in frequency. -/
theorem actualBWeightedTiltedReference_decoded_inner (data : AnnularForcing lower × AnnularBoundary) :
    annularEnergyTrace lower length positive collar lengthPositive 0
      (bEnergyDecode lower length positive
        (annularTiltVariationalInverse parameters lower length positive collar lengthPositive widthHalf widthLength data)) =
      realLpDiagonal (fun mode : HighAnnularMode => Real.sqrt (highMultiplier mode.val.1))
        1 (by norm_num) bEnergyDecode_bound data.2 := by
  rw [bEnergyDecode, annularEnergyTrace_diagonal]
  exact congrArg (realLpDiagonal (fun mode : HighAnnularMode => Real.sqrt (highMultiplier mode.val.1))
    1 (by norm_num) bEnergyDecode_bound)
    (annularTiltVariationalSolution_inner parameters lower length positive collar lengthPositive widthHalf widthLength data.1 data.2)

end Consumer
end Grad.AnnularTiltedReference
