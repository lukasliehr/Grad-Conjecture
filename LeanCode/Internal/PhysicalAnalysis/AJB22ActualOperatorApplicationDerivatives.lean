import AJB14GenuineFourierGeneratorExtraction
import Mathlib.Analysis.Calculus.ContDiff.Bounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators ContDiff
namespace Grad.AnnularOrbitGenerators

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

/-- Evaluation keeps the physical complex-linear operators while the orbit
and all differentiations use the real parameter. -/
def realComplexEvaluation : (E →L[ℂ] F) →L[ℝ] E →L[ℝ] F :=
  ((ContinuousLinearMap.apply ℂ F).flip.bilinearRestrictScalars ℝ)

theorem realComplexEvaluation_apply (operator : E →L[ℂ] F) (field : E) :
    realComplexEvaluation operator field = operator field := rfl

theorem realComplexEvaluation_norm : ‖realComplexEvaluation (E := E) (F := F)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro operator
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro field
  change ‖operator field‖ ≤ (1 * ‖operator‖) * ‖field‖
  simpa only [one_mul] using operator.le_opNorm field

/-- The genuine iterated derivative of an operator applied to moving data
has the binomial Leibniz norm bound. No regularity is inferred from translations. -/
theorem iteratedDeriv_operatorApplication_bound (operator : ℝ → E →L[ℂ] F) (data : ℝ → E)
    (operatorSmooth : ContDiff ℝ ∞ operator) (dataSmooth : ContDiff ℝ ∞ data)
    (order : ℕ) (time : ℝ) :
    ‖iteratedDeriv order (fun parameter => operator parameter (data parameter)) time‖ ≤
      ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) *
        ‖iteratedDeriv index operator time‖ * ‖iteratedDeriv (order - index) data time‖ := by
  have bound := (realComplexEvaluation (E := E) (F := F)).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    operatorSmooth dataSmooth time (n := order) (by exact_mod_cast (show (order : ℕ∞) ≤ ⊤ from le_top))
    realComplexEvaluation_norm
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, realComplexEvaluation_apply] using bound

end Grad.AnnularOrbitGenerators
