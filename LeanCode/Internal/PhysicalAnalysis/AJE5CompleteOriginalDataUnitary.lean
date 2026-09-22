import AJE4OriginalBoundaryCharacters

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 300000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.SourceCollarFullSource Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularLowEnergy Grad.AnnularLowOrbit

/-- Restriction of a complex character isometry to the real source structure. -/
def realCharacterEquivalence {E : Type*} [NormedAddCommGroup E] [Module ℂ E]
    [Module ℝ E] [IsScalarTower ℝ ℂ E] (mapping : E ≃ₗᵢ[ℂ] E) : E ≃ₗᵢ[ℝ] E where
  toLinearEquiv := mapping.toLinearEquiv.restrictScalars ℝ
  norm_map' := mapping.norm_map

variable (parameters : PhaseParameters) (lower : ℝ) (angular cell : ℕ)

/-- The same genuine Fourier character on all seven original source datum
coordinates, keeping both source graphs and every original trace norm. -/
def originalDataAmbientTranslation (tau : OrbitParameter) :
    OriginalStrongAmbient parameters lower angular cell ≃ₗᵢ[ℝ]
      OriginalStrongAmbient parameters lower angular cell :=
  realHilbertProductEquivalence
    (realHilbertProductEquivalence
      (realHilbertProductEquivalence (sourceGraphTranslationEquivalence 1 lower tau)
        (sourceGraphTranslationEquivalence 1 lower tau))
      (realHilbertProductEquivalence (realCharacterEquivalence (orbitLpEquivalence (RadialL2 1 lower) tau))
        (realCharacterEquivalence (orbitLpEquivalence (RadialL2 1 lower) tau))))
    (realHilbertProductEquivalence (realCharacterEquivalence (outerDatumTranslationEquivalence parameters angular cell tau))
      (realHilbertProductEquivalence (realCharacterEquivalence (highIncomingTranslationEquivalence tau))
        (realCharacterEquivalence (lowBoundaryTranslationEquivalence tau))))

theorem originalDataAmbientTranslation_exact (tau : OrbitParameter)
    (data : OriginalStrongAmbient parameters lower angular cell) :
    originalDataAmbientTranslation parameters lower angular cell tau data =
      WithLp.toLp 2
        (WithLp.toLp 2
          (WithLp.toLp 2 (sourceGraphTranslation 1 lower tau data.ofLp.1.ofLp.1.ofLp.1,
            sourceGraphTranslation 1 lower tau data.ofLp.1.ofLp.1.ofLp.2),
          WithLp.toLp 2 (orbitLpAction (RadialL2 1 lower) tau data.ofLp.1.ofLp.2.ofLp.1,
            orbitLpAction (RadialL2 1 lower) tau data.ofLp.1.ofLp.2.ofLp.2)),
        WithLp.toLp 2 (outerDatumTranslation parameters angular cell tau data.ofLp.2.ofLp.1,
          WithLp.toLp 2 (highIncomingTranslation tau data.ofLp.2.ofLp.2.ofLp.1,
            lowBoundaryTranslation tau data.ofLp.2.ofLp.2.ofLp.2))) := rfl

theorem originalDataAmbientTranslation_symm (tau : OrbitParameter)
    (data : OriginalStrongAmbient parameters lower angular cell) :
    (originalDataAmbientTranslation parameters lower angular cell tau).symm data =
      originalDataAmbientTranslation parameters lower angular cell (-tau) data := rfl

theorem originalDataAmbientTranslation_mem (tau : OrbitParameter)
    (data : OriginalStrongCarrier parameters lower angular cell) :
    originalDataAmbientTranslation parameters lower angular cell tau data.val ∈
      OriginalStrongCarrier parameters lower angular cell := by
  have mean := OriginalStrongCarrier.mean_free parameters lower angular cell data
  have f2Mean : meanFreeRow lower (originalF2Projection parameters lower angular cell
      (originalDataAmbientTranslation parameters lower angular cell tau data.val)) =
      originalF2Projection parameters lower angular cell
        (originalDataAmbientTranslation parameters lower angular cell tau data.val) := by
    apply (meanFreeRow_fixed_iff lower _).mpr
    intro mode zero
    change unweightedSourceF2Bulk parameters lower
      (sourceGraphTranslation 1 lower tau data.val.ofLp.1.ofLp.1.ofLp.2) mode = 0
    rw [unweightedSourceF2Bulk_translation,orbitLpAction_apply,mean.1 mode zero,smul_zero]
  have fMean : meanFreeRow lower (originalFProjection parameters lower angular cell
      (originalDataAmbientTranslation parameters lower angular cell tau data.val)) =
      originalFProjection parameters lower angular cell
        (originalDataAmbientTranslation parameters lower angular cell tau data.val) := by
    apply (meanFreeRow_fixed_iff lower _).mpr
    intro mode zero
    change orbitCharacter tau mode • data.val.ofLp.1.ofLp.2.ofLp.1 mode = 0
    rw [mean.2.1 mode zero,smul_zero]
  have gMean : meanFreeRow lower (originalGProjection parameters lower angular cell
      (originalDataAmbientTranslation parameters lower angular cell tau data.val)) =
      originalGProjection parameters lower angular cell
        (originalDataAmbientTranslation parameters lower angular cell tau data.val) := by
    apply (meanFreeRow_fixed_iff lower _).mpr
    intro mode zero
    change orbitCharacter tau mode • data.val.ofLp.1.ofLp.2.ofLp.2 mode = 0
    rw [mean.2.2 mode zero,smul_zero]
  exact ⟨⟨sub_eq_zero.mpr f2Mean,sub_eq_zero.mpr fMean⟩,sub_eq_zero.mpr gMean⟩

/-- The actual original strong datum is translated within its complete
mean-free carrier; this is an isometry at the unchanged analytic width. -/
def originalDataTranslation (tau : OrbitParameter) :
    OriginalStrongCarrier parameters lower angular cell →L[ℝ]
      OriginalStrongCarrier parameters lower angular cell :=
  ((originalDataAmbientTranslation parameters lower angular cell tau).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (OriginalStrongCarrier parameters lower angular cell).subtypeL).codRestrict
    (OriginalStrongCarrier parameters lower angular cell)
    (originalDataAmbientTranslation_mem parameters lower angular cell tau)

theorem originalDataTranslation_val (tau : OrbitParameter)
    (data : OriginalStrongCarrier parameters lower angular cell) :
    (originalDataTranslation parameters lower angular cell tau data).val =
      originalDataAmbientTranslation parameters lower angular cell tau data.val := rfl

theorem originalDataTranslation_inverse (tau : OrbitParameter)
    (data : OriginalStrongCarrier parameters lower angular cell) :
    originalDataTranslation parameters lower angular cell tau
      (originalDataTranslation parameters lower angular cell (-tau) data) = data := by
  apply Subtype.ext
  exact (originalDataAmbientTranslation parameters lower angular cell tau).apply_symm_apply data.val

theorem originalDataTranslation_norm (tau : OrbitParameter)
    (data : OriginalStrongCarrier parameters lower angular cell) :
    ‖originalDataTranslation parameters lower angular cell tau data‖ = ‖data‖ :=
  (originalDataAmbientTranslation parameters lower angular cell tau).norm_map data.val

def originalDataTranslationEquivalence (tau : OrbitParameter) :
    OriginalStrongCarrier parameters lower angular cell ≃ₗᵢ[ℝ]
      OriginalStrongCarrier parameters lower angular cell where
  toLinearEquiv :=
    { (originalDataTranslation parameters lower angular cell tau).toLinearMap with
      invFun := originalDataTranslation parameters lower angular cell (-tau)
      left_inv := by
        intro data
        change originalDataTranslation parameters lower angular cell (-tau)
          (originalDataTranslation parameters lower angular cell tau data) = data
        simpa only [neg_neg] using originalDataTranslation_inverse parameters lower angular cell (-tau) data
      right_inv := originalDataTranslation_inverse parameters lower angular cell tau }
  norm_map' := originalDataTranslation_norm parameters lower angular cell tau

end Grad.AnnularStrongOrbit
