import AKBE16RadialProjectionLocality

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.ActualCartesianWeakEquations
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianStartup
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- The actual radial projector has its compact-test transpose for fields
continuous only on the punctured disk. No derivative L2 or axis regularity
is required; the existing cutoff localizes all relevant circles. -/
theorem puncturedRadialProjection_rawTranspose (raw : Spatial → ComplexEuclidean 2)
    (continuousRaw : ContinuousOn raw (openUnitDisk \ {(0 : Spatial)}))
    (source : Fin 2) (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test)
    (compact : HasCompactSupport test) (supported : tsupport test ⊆ openUnitDisk)
    (away : (0 : Spatial) ∉ tsupport test) :
    (∫ point in openUnitDisk, test point • closedFieldExtension
      (closedRadialReflectionValue (fun closed : ClosedDisk => raw closed.val)) point source) =
      ∑ target : Fin 2, ∫ point in openUnitDisk,
        startupRawQradTest source test target point • raw point target := by
  obtain ⟨localized,continuousLocal,same⟩ := originalTest_continuousLocalization raw continuousRaw test supported away
  let closedRaw : ClosedDisk → ComplexEuclidean 2 := fun point => raw point.val
  let closedLocal : ClosedDisk → ComplexEuclidean 2 := fun point => localized point.val
  have continuousClosed : Continuous closedLocal := continuousLocal.comp continuous_subtype_val
  calc
    _ = ∫ point in openUnitDisk, test point •
        closedFieldExtension (closedRadialReflectionValue closedLocal) point source := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point inside
      by_cases zero : test point = 0
      · rw [zero,zero_smul,zero_smul]
      let closed : ClosedDisk := ⟨point,by change ‖point‖ ≤ 1; exact inside.le⟩
      have localSame : ∀ other : ClosedDisk, ‖other.val‖ = ‖closed.val‖ → closedRaw other = closedLocal other := by
        intro other normSame
        exact (same point (subset_tsupport test zero) other.val normSame).symm
      have equal := closedRadialReflectionValue_norm_locality closedRaw closedLocal closed localSame
      have firstAt := closedFieldExtension_value (closedRadialReflectionValue closedRaw) closed
      have secondAt := closedFieldExtension_value (closedRadialReflectionValue closedLocal) closed
      change test point • (closedFieldExtension (closedRadialReflectionValue closedRaw) point) source = _
      rw [firstAt,secondAt,equal]
    _ = ∑ target : Fin 2, ∫ point in openUnitDisk,
        startupRawQradTest source test target point • closedFieldExtension closedLocal point target :=
      closedRadialProjection_rawTranspose closedLocal continuousClosed source test smooth compact
    _ = _ := by
      apply Finset.sum_congr rfl
      intro target _
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point inside
      by_cases zero : startupRawQradTest source test target point = 0
      · rw [zero,zero_smul,zero_smul]
      obtain ⟨other,membership,normSame⟩ := originalRawQradTest_nonzero_support source target test point zero
      let closed : ClosedDisk := ⟨point,by change ‖point‖ ≤ 1; exact inside.le⟩
      have closedAt := closedFieldExtension_value closedLocal closed
      have localSame := same other membership point normSame.symm
      change localized point = raw point at localSame
      change closedFieldExtension closedLocal point = localized point at closedAt
      rw [closedAt,localSame]

end Grad.ActualCartesianWeakEquations
