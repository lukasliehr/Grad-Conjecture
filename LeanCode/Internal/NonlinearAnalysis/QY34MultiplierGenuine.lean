import Q24CoefficientFieldBilinear
import Q23MixedInnerZeroth
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

open Filter
open scoped Topology

namespace Grad.MixedQuotientComposition

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.NonlinearQuotientBounds
open Grad.Q24Realization

/-- Exact transfer between a core seminorm quotient and its isometric
Banach embedding, with the original complex reciprocal and real line. -/
theorem coreCurve_hasDerivAt_iff {Core E : Type*}
    [AddCommGroup Core] [Module ℂ Core]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    (embedding : Core →ₗ[ℂ] E) (coreNorm : Core → ℝ)
    (normIdentity : ∀ value, ‖embedding value‖ = coreNorm value)
    (curve : ℝ → Core) (derivative : Core) :
    HasDerivAt (fun t : ℝ => embedding (curve t)) (embedding derivative) 0 ↔
      Tendsto (fun t : ℝ => coreNorm (((t : ℂ)⁻¹ • (curve t - curve 0)) - derivative))
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  rw [hasDerivAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
  have identity : (fun t : ℝ => ‖slope (fun r : ℝ => embedding (curve r)) 0 t - embedding derivative‖) =
      fun t : ℝ => coreNorm (((t : ℂ)⁻¹ • (curve t - curve 0)) - derivative) := by
    funext t
    rw [slope_def_module, sub_zero, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    change ‖((t⁻¹ : ℝ) : ℂ) • (embedding (curve t) - embedding (curve 0)) - embedding derivative‖ = _
    rw [Complex.ofReal_inv, ← map_sub, ← map_smul, ← map_sub, normIdentity]
  rw [identity]

/-- The genuine product rule for the literal coefficient action when both
the root coefficient and the seed field vary. No product estimate or
derivative conclusion is assumed: it follows from their actual completions. -/
theorem multiplier_curve_genuine (parameters : PhaseParameters)
    (coefficient : ℝ → TameCoefficient parameters) (coefficientDerivative : TameCoefficient parameters)
    (field : ℝ → ACore parameters 3) (fieldDerivative : ACore parameters 3)
    (coefficientGenuine : HasEnvDerivAt coefficient coefficientDerivative)
    (fieldGenuine : ∀ grade, Tendsto (fun t : ℝ => originalGradeNorm grade
      (((t : ℂ)⁻¹ • (field t - field 0)) - fieldDerivative))
      (𝓝[≠] (0 : ℝ)) (𝓝 0)) :
    ∀ grade, Tendsto (fun t : ℝ => originalGradeNorm grade
      (((t : ℂ)⁻¹ • (tameScalarMultiplier 3 (coefficient t) (field t) -
        tameScalarMultiplier 3 (coefficient 0) (field 0))) -
        (tameScalarMultiplier 3 coefficientDerivative (field 0) +
          tameScalarMultiplier 3 (coefficient 0) fieldDerivative)))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  intro grade
  have coefficientRule := (coreCurve_hasDerivAt_iff (Grad.Q8FixedGrade.embed parameters grade)
    (coefficientEnvelope grade) (Grad.Q8FixedGrade.embed_norm parameters grade)
    coefficient coefficientDerivative).2 (coefficientGenuine grade)
  have fieldRule := (coreCurve_hasDerivAt_iff (fieldEmbed parameters 3 grade)
    (originalGradeNorm grade) (fieldEmbed_norm parameters 3 grade) field fieldDerivative).2
      (fieldGenuine grade)
  let realAction := (q23RestrictScalarsCLM
    (E := Grad.Q8FixedGrade.Carrier parameters grade) (F := AGrade parameters 3 grade)).comp
      ((completedCoefficientField parameters 3 grade).restrictScalars ℝ)
  have operatorRule := realAction.hasFDerivAt.comp_hasDerivAt 0 fieldRule
  have productRule := operatorRule.clm_apply coefficientRule
  have actionCore (a : TameCoefficient parameters) (v : ACore parameters 3) :
      realAction (fieldEmbed parameters 3 grade v) (Grad.Q8FixedGrade.embed parameters grade a) =
        fieldEmbed parameters 3 grade (tameScalarMultiplier 3 a v) := by
    change completedCoefficientField parameters 3 grade (fieldEmbed parameters 3 grade v)
      (Grad.Q8FixedGrade.embed parameters grade a) = _
    rw [completedCoefficientField_core, coefficientFieldMap_core]
  have productRule' : HasDerivAt
      (fun t : ℝ => fieldEmbed parameters 3 grade (tameScalarMultiplier 3 (coefficient t) (field t)))
      (fieldEmbed parameters 3 grade
        (tameScalarMultiplier 3 coefficientDerivative (field 0) +
          tameScalarMultiplier 3 (coefficient 0) fieldDerivative)) 0 := by
    simpa only [Function.comp_apply, actionCore, map_add, add_comm] using productRule
  exact (coreCurve_hasDerivAt_iff (fieldEmbed parameters 3 grade)
    (originalGradeNorm grade) (fieldEmbed_norm parameters 3 grade) _ _).1 productRule'

end Grad.MixedQuotientComposition
