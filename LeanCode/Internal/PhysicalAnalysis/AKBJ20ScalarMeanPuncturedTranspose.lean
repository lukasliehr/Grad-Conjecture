import AKBJ18ScalarMeanClosedTranspose

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.ActualScalarWeakEquations
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianStartup Grad.CartesianState
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.ActualCartesianWeakEquations

private theorem scalarContinuousLocalization (raw : Spatial → ComplexEuclidean 1)
    (continuousRaw : ContinuousOn raw (openUnitDisk \ {(0 : Spatial)}))
    (test : Spatial → ℝ) (supported : tsupport test ⊆ openUnitDisk)
    (away : (0 : Spatial) ∉ tsupport test) :
    ∃ localized : Spatial → ComplexEuclidean 1, Continuous localized ∧
      ∀ point ∈ tsupport test, ∀ other : Spatial, ‖other‖ = ‖point‖ → localized other = raw other := by
  obtain ⟨cutoff,smooth,_,cutoffSupported,oneOn⟩ := originalTest_radialCutoff test supported away
  refine ⟨fun point => cutoff point • raw point,
    continuous_smul_of_tsupport_subset _ (openUnitDisk_isOpen.sdiff isClosed_singleton)
      cutoff smooth.continuous cutoffSupported raw continuousRaw,?_⟩
  intro point membership other sameNorm
  change cutoff other • raw other = raw other
  rw [oneOn point membership other sameNorm,one_smul]

private theorem scalarMean_norm_locality (first second : ClosedDisk → ComplexEuclidean 1) (point : ClosedDisk)
    (same : ∀ other : ClosedDisk, ‖other.val‖ = ‖point.val‖ → first other = second other) :
    closedAngularMean first point = closedAngularMean second point := by
  unfold closedAngularMean
  apply integral_congr_ae
  filter_upwards [] with time
  exact same _ (radialRotatedPoint_norm _ point)

/-- Mean transpose support stays on circles intersecting the original compact support. -/
theorem scalarMeanTest_nonzero_support (test : Spatial → ℝ) (point : Spatial)
    (nonzero : startupAngularTest (fun _ => 1) test point ≠ 0) :
    ∃ other ∈ tsupport test, ‖other‖ = ‖point‖ := by
  classical
  by_contra absent
  have vanishes (other : Spatial) (sameNorm : ‖other‖ = ‖point‖) : test other = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro membership
    exact absent ⟨other,membership,sameNorm⟩
  apply nonzero
  unfold startupAngularTest
  simp only [vanishes _ (LinearIsometryEquiv.norm_map _ _),mul_zero,integral_zero,mul_zero]

/-- The literal scalar mean transpose is valid for a field smooth only off the axis. -/
theorem scalarMean_puncturedTranspose (raw : Spatial → ComplexEuclidean 1)
    (continuousRaw : ContinuousOn raw (openUnitDisk \ {(0 : Spatial)}))
    (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test)
    (compact : HasCompactSupport test) (supported : tsupport test ⊆ openUnitDisk)
    (away : (0 : Spatial) ∉ tsupport test) :
    (∫ point in openUnitDisk, test point • (closedFieldExtension
      (closedAngularMean (fun closed : ClosedDisk => raw closed.val)) point) 0) =
      ∫ point in openUnitDisk, startupAngularTest (fun _ => 1) test point • raw point 0 := by
  obtain ⟨localized,continuousLocal,same⟩ := scalarContinuousLocalization raw continuousRaw test supported away
  let closedRaw : ClosedDisk → ComplexEuclidean 1 := fun point => raw point.val
  let closedLocal : ClosedDisk → ComplexEuclidean 1 := fun point => localized point.val
  have continuousClosed : Continuous closedLocal := continuousLocal.comp continuous_subtype_val
  calc
    _ = ∫ point in openUnitDisk, test point •
        (closedFieldExtension (closedAngularMean closedLocal) point) 0 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point inside
      by_cases zero : test point = 0
      · rw [zero,zero_smul,zero_smul]
      let closed : ClosedDisk := ⟨point,by change ‖point‖ ≤ 1; exact inside.le⟩
      have localSame : ∀ other : ClosedDisk, ‖other.val‖ = ‖closed.val‖ → closedRaw other = closedLocal other := by
        intro other normSame
        exact (same point (subset_tsupport test zero) other.val normSame).symm
      have equal := scalarMean_norm_locality closedRaw closedLocal closed localSame
      have firstAt := closedFieldExtension_value (closedAngularMean closedRaw) closed
      have secondAt := closedFieldExtension_value (closedAngularMean closedLocal) closed
      change test point • (closedFieldExtension (closedAngularMean closedRaw) point) 0 = _
      rw [firstAt,secondAt,equal]
    _ = ∫ point in openUnitDisk, startupAngularTest (fun _ => 1) test point •
        (closedFieldExtension closedLocal point) 0 := scalarMean_closedTranspose closedLocal continuousClosed test smooth compact
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point inside
      by_cases zero : startupAngularTest (fun _ => 1) test point = 0
      · rw [zero,zero_smul,zero_smul]
      obtain ⟨other,membership,normSame⟩ := scalarMeanTest_nonzero_support test point zero
      let closed : ClosedDisk := ⟨point,by change ‖point‖ ≤ 1; exact inside.le⟩
      have closedAt := closedFieldExtension_value closedLocal closed
      have localSame := same other membership point normSame.symm
      change localized point = raw point at localSame
      change closedFieldExtension closedLocal point = localized point at closedAt
      rw [closedAt,localSame]

end Grad.ActualScalarWeakEquations
