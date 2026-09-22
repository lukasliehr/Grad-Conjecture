import AIZ3ActualLowTranslations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularCoupledOrbit
open Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCoupledInverse Grad.AnnularCrossMaps

section Product
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The literal Hilbert product of two norm-isometric translations. -/
def hilbertProductEquivalence (first : E ≃ₗᵢ[ℂ] E) (second : F ≃ₗᵢ[ℂ] F) :
    WithLp 2 (E × F) ≃ₗᵢ[ℂ] WithLp 2 (E × F) where
  toLinearEquiv :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ E F).toLinearEquiv.trans
      ((first.toLinearEquiv.prodCongr second.toLinearEquiv).trans
        (WithLp.prodContinuousLinearEquiv 2 ℂ E F).symm.toLinearEquiv)
  norm_map' := by
    intro field
    change ‖WithLp.toLp 2 (first field.ofLp.1, second field.ofLp.2)‖ = ‖field‖
    have output := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (first field.ofLp.1, second field.ofLp.2))
    have input := WithLp.prod_norm_sq_eq_of_L2 field
    change ‖field‖ ^ 2 = ‖field.ofLp.1‖ ^ 2 + ‖field.ofLp.2‖ ^ 2 at input
    change ‖WithLp.toLp 2 (first field.ofLp.1, second field.ofLp.2)‖ ^ 2 =
      ‖first field.ofLp.1‖ ^ 2 + ‖second field.ofLp.2‖ ^ 2 at output
    rw [first.norm_map, second.norm_map] at output
    nlinarith [norm_nonneg field, norm_nonneg (WithLp.toLp 2 (first field.ofLp.1, second field.ofLp.2))]

theorem hilbertProductEquivalence_apply (first : E ≃ₗᵢ[ℂ] E) (second : F ≃ₗᵢ[ℂ] F)
    (field : WithLp 2 (E × F)) :
    hilbertProductEquivalence first second field = WithLp.toLp 2 (first field.ofLp.1, second field.ofLp.2) := rfl

theorem hilbertProductEquivalence_symm_apply (first : E ≃ₗᵢ[ℂ] E) (second : F ≃ₗᵢ[ℂ] F)
    (field : WithLp 2 (E × F)) :
    (hilbertProductEquivalence first second).symm field = WithLp.toLp 2 (first.symm field.ofLp.1, second.symm field.ofLp.2) := rfl

end Product

variable (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)

/-- Exact translation of the complete original W and Domega high pair. -/
def highTranslationEquivalence (tau : OrbitParameter) :
    CrossHighSpace lower length positive lengthPositive ≃ₗᵢ[ℂ] CrossHighSpace lower length positive lengthPositive :=
  hilbertProductEquivalence (energyTranslationEquivalence lower length positive tau)
    (fluxTranslationEquivalence lower length positive lengthPositive tau)

/-- The same original complete coupled solution space, with no change of
radial weight, analytic width, graph domain, or tangential grade. -/
def coupledTranslationEquivalence (tau : OrbitParameter) :
    CoupledSpace lower length positive lengthPositive ≃ₗᵢ[ℂ] CoupledSpace lower length positive lengthPositive :=
  hilbertProductEquivalence (highTranslationEquivalence lower length positive lengthPositive tau)
    (lowTranslationEquivalence lower length positive tau)

theorem coupledTranslation_apply (tau : OrbitParameter) (field : CoupledSpace lower length positive lengthPositive) :
    coupledTranslationEquivalence lower length positive lengthPositive tau field =
      WithLp.toLp 2 (WithLp.toLp 2
        (energyTranslation lower length positive tau field.ofLp.1.ofLp.1,
          fluxTranslation lower length positive lengthPositive tau field.ofLp.1.ofLp.2),
        lowTranslation lower length positive tau field.ofLp.2) := rfl

theorem coupledTranslation_symm (tau : OrbitParameter) (field : CoupledSpace lower length positive lengthPositive) :
    (coupledTranslationEquivalence lower length positive lengthPositive tau).symm field =
      coupledTranslationEquivalence lower length positive lengthPositive (-tau) field := rfl

theorem coupledTranslation_add (tau sigma : OrbitParameter) (field : CoupledSpace lower length positive lengthPositive) :
    coupledTranslationEquivalence lower length positive lengthPositive (tau + sigma) field =
      coupledTranslationEquivalence lower length positive lengthPositive tau
        (coupledTranslationEquivalence lower length positive lengthPositive sigma field) := by
  simp only [coupledTranslation_apply]
  congr 2
  · congr 2
    · exact energyTranslation_add lower length positive tau sigma field.ofLp.1.ofLp.1
    · exact fluxTranslation_add lower length positive lengthPositive tau sigma field.ofLp.1.ofLp.2
  · exact lowTranslation_add lower length positive tau sigma field.ofLp.2

end Grad.AnnularCoupledOrbit
