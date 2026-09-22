import AJE5CompleteOriginalDataUnitary

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 300000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularLowEnergy Grad.AnnularLowOrbit

section Finite
variable {E : Type*} [NormedAddCommGroup E] [Module ℝ E] (n : ℕ)

def finiteRealHilbertEquivalence (mapping : E ≃ₗᵢ[ℝ] E) :
    PiLp 2 (fun _ : Fin n => E) ≃ₗᵢ[ℝ] PiLp 2 (fun _ : Fin n => E) where
  toFun field := WithLp.toLp 2 (fun slot => mapping (field slot))
  invFun field := WithLp.toLp 2 (fun slot => mapping.symm (field slot))
  left_inv field := by
    apply PiLp.ext
    intro slot
    exact mapping.symm_apply_apply (field slot)
  right_inv field := by
    apply PiLp.ext
    intro slot
    exact mapping.apply_symm_apply (field slot)
  map_add' first second := by
    apply PiLp.ext
    intro slot
    exact map_add mapping (first slot) (second slot)
  map_smul' scalar field := by
    apply PiLp.ext
    intro slot
    exact map_smul mapping scalar (field slot)
  norm_map' field := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro slot _
    change ‖mapping (field slot)‖ ^ 2 = ‖field slot‖ ^ 2
    rw [mapping.norm_map]

end Finite

variable (parameters : PhaseParameters) (lower : ℝ) (angular cell : ℕ)

/-- Literal character translation on the six shared forcing rows, the
redundant zero auxiliary slot, the two genuine source graphs, and the
three independently prescribed boundary blocks. -/
def strongDataAmbientTranslation (tau : OrbitParameter) :
    StrongDataAmbient parameters lower angular cell ≃ₗᵢ[ℝ]
      StrongDataAmbient parameters lower angular cell :=
  realHilbertProductEquivalence
    (realHilbertProductEquivalence
      (realHilbertProductEquivalence
        (finiteRealHilbertEquivalence 4 (realCharacterEquivalence (orbitLpEquivalence (RadialL2 1 lower) tau)))
        (finiteRealHilbertEquivalence 3 (realCharacterEquivalence (orbitLpEquivalence (RadialL2 1 lower) tau))))
      (realHilbertProductEquivalence
        (realHilbertProductEquivalence (sourceGraphTranslationEquivalence 1 lower tau)
          (sourceGraphTranslationEquivalence 1 lower tau))
        (realHilbertProductEquivalence (realCharacterEquivalence (outerDatumTranslationEquivalence parameters angular cell tau))
          (realCharacterEquivalence (highIncomingTranslationEquivalence tau)))))
    (realCharacterEquivalence (lowBoundaryTranslationEquivalence tau))

theorem strongDataAmbientTranslation_exact (tau : OrbitParameter)
    (data : StrongDataAmbient parameters lower angular cell) :
    strongDataAmbientTranslation parameters lower angular cell tau data =
      WithLp.toLp 2
        (WithLp.toLp 2
          (WithLp.toLp 2
            (WithLp.toLp 2 (fun slot => orbitLpAction (RadialL2 1 lower) tau (data.ofLp.1.ofLp.1.ofLp.1 slot)),
            WithLp.toLp 2 (fun slot => orbitLpAction (RadialL2 1 lower) tau (data.ofLp.1.ofLp.1.ofLp.2 slot))),
          WithLp.toLp 2
            (WithLp.toLp 2 (sourceGraphTranslation 1 lower tau data.ofLp.1.ofLp.2.ofLp.1.ofLp.1,
              sourceGraphTranslation 1 lower tau data.ofLp.1.ofLp.2.ofLp.1.ofLp.2),
            WithLp.toLp 2 (outerDatumTranslation parameters angular cell tau data.ofLp.1.ofLp.2.ofLp.2.ofLp.1,
              highIncomingTranslation tau data.ofLp.1.ofLp.2.ofLp.2.ofLp.2))),
        lowBoundaryTranslation tau data.ofLp.2) := rfl

theorem strongDataAmbientTranslation_symm (tau : OrbitParameter)
    (data : StrongDataAmbient parameters lower angular cell) :
    (strongDataAmbientTranslation parameters lower angular cell tau).symm data =
      strongDataAmbientTranslation parameters lower angular cell (-tau) data := rfl

end Grad.AnnularStrongOrbit
