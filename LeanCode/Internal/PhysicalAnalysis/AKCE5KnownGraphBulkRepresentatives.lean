import AKCE4ClosedRetainedSevenCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set Filter MeasureTheory
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularSourceGraph Grad.AnnularCurrentSource Grad.AnnularPhysicalReconstruction Grad.BoundaryKernelAction

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)

theorem knownF0Bulk_sameGraph (graph : AnnularTotalSourceH1 parameters 1 lower 1 0 0) (mode : ℤ×ℤ) :
    unweightedSourceF0Bulk parameters lower graph mode =
      radialSqrtMap 1 lower (totalConjugatedCoordinate parameters 1 lower positive bounded.le 1 0 0 graph mode 0) := by
  change (sourceGradeRatio 0 0 1 0 mode : ℝ) • weightedRadialCoordinate 1 lower 0 (graph mode)=_
  rw [totalConjugatedCoordinate_storage parameters 1 lower positive bounded.le 1 0 0 graph mode 0,smul_smul]
  have factor : sourceGradeRatio 0 0 1 0 mode * sourceInsertedWeight 1 0 0 mode=1 := by
    simp only [sourceInsertedWeight,pow_zero,one_mul,sourceGradeRatio]
    rw [div_mul_cancel₀ _ (splitTangentialWeight_pos 1 0 mode).ne']
    simp [splitTangentialWeight]
  rw [factor,one_smul]

theorem knownF2Bulk_sameGraph (graph : AnnularTotalSourceH1 parameters 1 lower 0 0 0) (mode : ℤ×ℤ) :
    unweightedSourceF2Bulk parameters lower graph mode =
      radialSqrtMap 1 lower (totalConjugatedCoordinate parameters 1 lower positive bounded.le 0 0 0 graph mode 0) := by
  change weightedRadialCoordinate 1 lower 0 (graph mode)=_
  rw [totalConjugatedCoordinate_storage parameters 1 lower positive bounded.le 0 0 0 graph mode 0]
  simp only [sourceInsertedWeight,splitTangentialWeight,pow_zero,one_mul,one_smul]

theorem knownF0Bulk_section_ae (graph : AnnularTotalSourceH1 parameters 1 lower 1 0 0) (mode : ℤ×ℤ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),unweightedSourceF0Bulk parameters lower graph mode radius=
      Real.sqrt radius • radialSectionExtension 1 lower bounded.le
        (totalConjugatedSection parameters 1 lower positive bounded 1 0 0 graph mode) radius := by
  rw [knownF0Bulk_sameGraph parameters lower positive bounded]
  filter_upwards [radialSqrtMap_ae 1 lower (totalConjugatedCoordinate parameters 1 lower positive bounded.le 1 0 0 graph mode 0),
    totalConjugatedSection_ae parameters 1 lower positive bounded 1 0 0 graph mode] with radius storage same
  exact storage.trans (congrArg (fun value : ComplexEuclidean 1 => Real.sqrt radius • value) same.symm)

theorem knownF2Bulk_section_ae (graph : AnnularTotalSourceH1 parameters 1 lower 0 0 0) (mode : ℤ×ℤ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),unweightedSourceF2Bulk parameters lower graph mode radius=
      Real.sqrt radius • radialSectionExtension 1 lower bounded.le
        (totalConjugatedSection parameters 1 lower positive bounded 0 0 0 graph mode) radius := by
  rw [knownF2Bulk_sameGraph parameters lower positive bounded]
  filter_upwards [radialSqrtMap_ae 1 lower (totalConjugatedCoordinate parameters 1 lower positive bounded.le 0 0 0 graph mode 0),
    totalConjugatedSection_ae parameters 1 lower positive bounded 0 0 0 graph mode] with radius storage same
  exact storage.trans (congrArg (fun value : ComplexEuclidean 1 => Real.sqrt radius • value) same.symm)

theorem knownRF0Bulk_section_ae (graph : AnnularTotalSourceH1 parameters 1 lower 1 0 0) (mode : ℤ×ℤ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),unweightedSourceRF0Bulk parameters lower graph mode radius=
      (Complex.I*(mode.1:ℂ)) • (Real.sqrt radius • radialSectionExtension 1 lower bounded.le
        (totalConjugatedSection parameters 1 lower positive bounded 1 0 0 graph mode) radius) := by
  filter_upwards [unweightedSourceRF0Bulk_genuine_ae parameters lower graph,
    knownF0Bulk_section_ae parameters lower positive bounded graph mode] with radius derivative same
  rw [derivative mode,same]

end Grad.OriginalCoreRealization
