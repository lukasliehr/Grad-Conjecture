import AJD2ActualBoundaryInverseOrbit
import AIZ4CompleteCoupledUnitary

noncomputable section
set_option autoImplicit false
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularCrossMaps Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit
open Grad.ActualBoundaryPrimitives

section Indexed
variable {Index E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (mode : Index → ℤ × ℤ)

def indexedTranslationLinear (tau : OrbitParameter) : lp (fun _ : Index => E) 2 →ₗ[ℂ] lp (fun _ : Index => E) 2 where
  toFun field := ⟨fun index => orbitCharacter tau (mode index) • field index,
    field.property.mono' (fun index => by rw [norm_smul, orbitCharacter_norm, one_mul])⟩
  map_add' first second := by
    apply lp.ext
    funext index
    exact smul_add _ _ _
  map_smul' scalar field := by
    apply lp.ext
    funext index
    exact smul_comm _ _ _

theorem indexedTranslation_norm (tau : OrbitParameter) (field : lp (fun _ : Index => E) 2) :
    ‖indexedTranslationLinear mode tau field‖ = ‖field‖ := by
  have point (index : Index) : ‖indexedTranslationLinear mode tau field index‖ = ‖field index‖ := by
    change ‖orbitCharacter tau (mode index) • field index‖ = _
    rw [norm_smul, orbitCharacter_norm, one_mul]
  exact le_antisymm (lp.norm_mono (by norm_num) (fun index => (point index).le))
    (lp.norm_mono (by norm_num) (fun index => (point index).ge))

def indexedTranslationEquivalence (tau : OrbitParameter) :
    lp (fun _ : Index => E) 2 ≃ₗᵢ[ℂ] lp (fun _ : Index => E) 2 where
  toLinearEquiv :=
    { indexedTranslationLinear mode tau with
      invFun := indexedTranslationLinear mode (-tau)
      left_inv := by
        intro field
        apply lp.ext
        funext index
        change orbitCharacter (-tau) (mode index) • (orbitCharacter tau (mode index) • field index) = field index
        rw [smul_smul, mul_comm, orbitCharacter_inverse, one_smul]
      right_inv := by
        intro field
        apply lp.ext
        funext index
        change orbitCharacter tau (mode index) • (orbitCharacter (-tau) (mode index) • field index) = field index
        rw [smul_smul, orbitCharacter_inverse, one_smul] }
  norm_map' := indexedTranslation_norm mode tau
end Indexed

variable (parameters : PhaseParameters) (lower : ℝ)

def highBulkTranslationEquivalence (tau : OrbitParameter) : AnnularBulk lower ≃ₗᵢ[ℂ] AnnularBulk lower :=
  indexedTranslationEquivalence (E := RadialL2 1 lower) (fun mode : HighAnnularMode => mode.val) tau

def highBulkTranslation (tau : OrbitParameter) : AnnularBulk lower →L[ℂ] AnnularBulk lower :=
  (highBulkTranslationEquivalence lower tau).toContinuousLinearEquiv.toContinuousLinearMap

def crossBulkTranslationEquivalence (tau : OrbitParameter) : CrossHighBulk lower ≃ₗᵢ[ℂ] CrossHighBulk lower :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin 3 => highBulkTranslationEquivalence lower tau)

/-- The exact Hilbert datum (f,qc,rqv,beta), retaining original trace and radial weights. -/
def crossDataTranslationEquivalence (tau : OrbitParameter) :
    CrossHighData parameters lower ≃ₗᵢ[ℂ] CrossHighData parameters lower :=
  hilbertProductEquivalence (crossBulkTranslationEquivalence lower tau) (highBoundaryTranslationEquivalence parameters tau)

def crossDataTranslation (tau : OrbitParameter) : CrossHighData parameters lower →L[ℂ] CrossHighData parameters lower :=
  (crossDataTranslationEquivalence parameters lower tau).toContinuousLinearEquiv.toContinuousLinearMap

theorem crossDataTranslation_bulk (tau : OrbitParameter) (datum : CrossHighData parameters lower)
    (row : Fin 3) (mode : HighAnnularMode) :
    (crossDataTranslation parameters lower tau datum).ofLp.1 row mode =
      orbitCharacter tau mode.val • datum.ofLp.1 row mode := rfl

theorem crossDataTranslation_boundary (tau : OrbitParameter) (datum : CrossHighData parameters lower) :
    (crossDataTranslation parameters lower tau datum).ofLp.2 = highBoundaryTranslation parameters tau datum.ofLp.2 := rfl

theorem crossDataTranslation_symm (tau : OrbitParameter) (datum : CrossHighData parameters lower) :
    (crossDataTranslationEquivalence parameters lower tau).symm datum =
      crossDataTranslation parameters lower (-tau) datum := rfl

theorem crossDataTranslation_inverse (tau : OrbitParameter) (datum : CrossHighData parameters lower) :
    crossDataTranslation parameters lower tau (crossDataTranslation parameters lower (-tau) datum) = datum :=
  (crossDataTranslationEquivalence parameters lower tau).apply_symm_apply datum

end Grad.AnnularCrossOrbit
