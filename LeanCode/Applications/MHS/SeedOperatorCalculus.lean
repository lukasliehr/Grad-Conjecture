import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section

open scoped ContDiff

namespace Grad.Constraints.Seed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def operatorExponentialApply (action : E →L[ℂ] (E →L[ℂ] E)) (identity : E) (value : E) : E :=
  (NormedSpace.exp (action value)) identity

theorem operatorExponentialApply_hasSum (action : E →L[ℂ] (E →L[ℂ] E)) (identity value : E) :
    HasSum (fun power : ℕ => ((power.factorial : ℂ)⁻¹) • (action value ^ power) identity)
      (operatorExponentialApply action identity value) := by
  have series : HasSum (fun power : ℕ => ((power.factorial : ℂ)⁻¹) • action value ^ power)
      (NormedSpace.exp (action value)) := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (action value)
  have evaluated := (ContinuousLinearMap.apply ℂ E identity).hasSum
    (f := fun power : ℕ => ((power.factorial : ℂ)⁻¹) • action value ^ power) series
  exact evaluated

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem operatorExponentialApply_contDiff (action : E →L[ℂ] (E →L[ℂ] E)) (identity : E) :
    ContDiff ℝ ∞ (operatorExponentialApply action identity) := by
  have exponentialComplex : ContDiff ℂ ∞ (NormedSpace.exp : (E →L[ℂ] E) → (E →L[ℂ] E)) := by
    rw [contDiff_iff_contDiffAt]
    intro operator
    exact (NormedSpace.exp_analytic (𝕂 := ℂ) operator).contDiffAt
  have exponentialSmooth : ContDiff ℝ ∞ (NormedSpace.exp : (E →L[ℂ] E) → (E →L[ℂ] E)) :=
    exponentialComplex.restrict_scalars ℝ
  exact ((ContinuousLinearMap.apply ℂ E identity).restrictScalars ℝ).contDiff.comp
    (exponentialSmooth.comp (action.restrictScalars ℝ).contDiff)

end Grad.Constraints.Seed
