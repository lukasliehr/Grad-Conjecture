import AJE3ExactSharedBulkOrbit
import AJB6GenuineLowTraceDataTranslations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularLowEnergy Grad.AnnularLowOrbit

section Product
variable {E F : Type*} [NormedAddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup F] [Module ℝ F]

/-- Real Hilbert product of the genuine component characters. -/
def realHilbertProductEquivalence (first : E ≃ₗᵢ[ℝ] E) (second : F ≃ₗᵢ[ℝ] F) :
    WithLp 2 (E × F) ≃ₗᵢ[ℝ] WithLp 2 (E × F) where
  toLinearEquiv :=
    (WithLp.linearEquiv 2 ℝ (E × F)).trans
      ((first.toLinearEquiv.prodCongr second.toLinearEquiv).trans
        (WithLp.linearEquiv 2 ℝ (E × F)).symm)
  norm_map' := by
    intro field
    change ‖WithLp.toLp 2 (first field.ofLp.1, second field.ofLp.2)‖ = ‖field‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2,WithLp.prod_norm_sq_eq_of_L2]
    change ‖first field.ofLp.1‖ ^ 2 + ‖second field.ofLp.2‖ ^ 2 =
      ‖field.ofLp.1‖ ^ 2 + ‖field.ofLp.2‖ ^ 2
    rw [first.norm_map,second.norm_map]

theorem realHilbertProductEquivalence_apply (first : E ≃ₗᵢ[ℝ] E) (second : F ≃ₗᵢ[ℝ] F)
    (field : WithLp 2 (E × F)) :
    realHilbertProductEquivalence first second field =
      WithLp.toLp 2 (first field.ofLp.1,second field.ofLp.2) := rfl

end Product

/-- Character on the actual prescribed high incoming trace. -/
def highIncomingTranslation (tau : OrbitParameter) : AnnularBoundary →L[ℂ] AnnularBoundary :=
  complexLpTwoMap (fun mode : HighAnnularMode =>
    orbitCharacter tau mode.val • ContinuousLinearMap.id ℂ (ComplexEuclidean 1)) 1 (by norm_num)
    (fun mode field => by
      change ‖orbitCharacter tau mode.val • field‖ ≤ 1 * ‖field‖
      rw [norm_smul,orbitCharacter_norm])

theorem highIncomingTranslation_apply (tau : OrbitParameter) (field : AnnularBoundary)
    (mode : HighAnnularMode) :
    highIncomingTranslation tau field mode = orbitCharacter tau mode.val • field mode := rfl

theorem highIncomingTranslation_inverse (tau : OrbitParameter) (field : AnnularBoundary) :
    highIncomingTranslation tau (highIncomingTranslation (-tau) field) = field := by
  apply lp.ext
  funext mode
  rw [highIncomingTranslation_apply,highIncomingTranslation_apply,smul_smul,orbitCharacter_inverse,one_smul]

theorem highIncomingTranslation_norm (tau : OrbitParameter) (field : AnnularBoundary) :
    ‖highIncomingTranslation tau field‖ = ‖field‖ := by
  have point (mode : HighAnnularMode) : ‖highIncomingTranslation tau field mode‖ = ‖field mode‖ := by
    rw [highIncomingTranslation_apply,norm_smul,orbitCharacter_norm,one_mul]
  exact le_antisymm (lp.norm_mono (by norm_num) (fun mode => (point mode).le))
    (lp.norm_mono (by norm_num) (fun mode => (point mode).ge))

def highIncomingTranslationEquivalence (tau : OrbitParameter) : AnnularBoundary ≃ₗᵢ[ℂ] AnnularBoundary where
  toLinearEquiv :=
    { (highIncomingTranslation tau).toLinearMap with
      invFun := highIncomingTranslation (-tau)
      left_inv := by
        intro field
        change highIncomingTranslation (-tau) (highIncomingTranslation tau field) = field
        simpa only [neg_neg] using highIncomingTranslation_inverse (-tau) field
      right_inv := highIncomingTranslation_inverse tau }
  norm_map' := highIncomingTranslation_norm tau

variable (parameters : PhaseParameters) (angular cell : ℕ)

theorem sourceNegativeCoefficient_translation {dimension : ℕ} (tau : OrbitParameter)
    (field : NegativeTrace parameters angular cell dimension) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell (orbitLpAction (ComplexEuclidean dimension) tau field) mode =
      orbitCharacter tau mode • negativeTraceCoefficient parameters angular cell field mode := by
  unfold negativeTraceCoefficient
  rw [orbitLpAction_apply]
  exact smul_comm _ _ _

/-- The original outer datum remains in its literal high angular sector. -/
def outerDatumTranslation (tau : OrbitParameter) :
    HighBoundaryPrimitive parameters angular cell →L[ℂ] HighBoundaryPrimitive parameters angular cell :=
  ((orbitLpAction (ComplexEuclidean 1) tau).comp
    (highAngularSubmodule parameters angular cell 1).subtypeL).codRestrict
    (highAngularSubmodule parameters angular cell 1) (by
      intro field mode low
      change negativeTraceCoefficient parameters angular cell
        (orbitLpAction (ComplexEuclidean 1) tau field.val) mode = 0
      rw [sourceNegativeCoefficient_translation,field.property mode low,smul_zero])

theorem outerDatumTranslation_val (tau : OrbitParameter) (field : HighBoundaryPrimitive parameters angular cell) :
    (outerDatumTranslation parameters angular cell tau field).val =
      orbitLpAction (ComplexEuclidean 1) tau field.val := rfl

theorem outerDatumTranslation_inverse (tau : OrbitParameter) (field : HighBoundaryPrimitive parameters angular cell) :
    outerDatumTranslation parameters angular cell tau
      (outerDatumTranslation parameters angular cell (-tau) field) = field := by
  apply Subtype.ext
  exact orbitLpAction_inverse (ComplexEuclidean 1) tau field.val

theorem outerDatumTranslation_norm (tau : OrbitParameter) (field : HighBoundaryPrimitive parameters angular cell) :
    ‖outerDatumTranslation parameters angular cell tau field‖ = ‖field‖ :=
  orbitLpLinear_norm (ComplexEuclidean 1) tau field.val

def outerDatumTranslationEquivalence (tau : OrbitParameter) :
    HighBoundaryPrimitive parameters angular cell ≃ₗᵢ[ℂ] HighBoundaryPrimitive parameters angular cell where
  toLinearEquiv :=
    { (outerDatumTranslation parameters angular cell tau).toLinearMap with
      invFun := outerDatumTranslation parameters angular cell (-tau)
      left_inv := by
        intro field
        change outerDatumTranslation parameters angular cell (-tau)
          (outerDatumTranslation parameters angular cell tau field) = field
        simpa only [neg_neg] using outerDatumTranslation_inverse parameters angular cell (-tau) field
      right_inv := outerDatumTranslation_inverse parameters angular cell tau }
  norm_map' := outerDatumTranslation_norm parameters angular cell tau

end Grad.AnnularStrongOrbit
