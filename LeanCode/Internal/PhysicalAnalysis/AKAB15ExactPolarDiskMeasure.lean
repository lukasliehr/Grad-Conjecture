import AKAB14PhysicalHilbertL1Consumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Grad.WeightedAxisRemoval
open Grad.ClosedJets Grad.DiskExtension.Operator

/-- The accepted Cartesian coordinate equivalence followed by the exact
polar Jacobian, at the level of nonnegative integrals. -/
theorem spatialPlane_lintegral_eq_polar (density : SpatialPlane → ℝ≥0∞) :
    (∫⁻ point : SpatialPlane, density point) =
      ∫⁻ point : ℝ × ℝ in polarCoord.target,
        ENNReal.ofReal point.1 * density (spatialPlaneOfPair (polarCoord.symm point)) := by
  have transformed := spatialPlaneCoordinate_measurePreserving.lintegral_comp_emb
    spatialPlaneCoordinateMeasurableEquiv.measurableEmbedding
    (fun point : ℝ × ℝ => density (spatialPlaneCoordinateMeasurableEquiv.symm point))
  have coordinate : (∫⁻ point : SpatialPlane, density point) =
      ∫⁻ point : ℝ × ℝ, density (spatialPlaneOfPair point) := by
    simpa only [spatialPlaneCoordinateMeasurableEquiv_symm,spatialPlaneOfPair_coordinateEquiv,Measure.volume_eq_prod] using transformed
  rw [coordinate]
  exact (lintegral_comp_polarCoord_symm (fun point => density (spatialPlaneOfPair point))).symm

theorem openDisk_lintegral_eq_polar (density : SpatialPlane → ℝ≥0∞) :
    (∫⁻ point in openUnitDisk, density point) =
      ∫⁻ point : ℝ × ℝ in Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal point.1 * density (spatialPlaneOfPair (polarCoord.symm point)) := by
  rw [← lintegral_indicator openUnitDisk_isOpen.measurableSet,spatialPlane_lintegral_eq_polar]
  have indicators : polarCoord.target.indicator
      (fun point : ℝ × ℝ => ENNReal.ofReal point.1 *
        openUnitDisk.indicator density (spatialPlaneOfPair (polarCoord.symm point))) =
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi).indicator
        (fun point : ℝ × ℝ => ENNReal.ofReal point.1 * density (spatialPlaneOfPair (polarCoord.symm point))) := by
    funext point
    by_cases target : point ∈ polarCoord.target
    · have radiusPositive : 0 < point.1 := target.1
      have disk : spatialPlaneOfPair (polarCoord.symm point) ∈ openUnitDisk ↔ point.1 < 1 := by
        change ‖spatialPlaneOfPair (polarCoord.symm point)‖ < 1 ↔ point.1 < 1
        rw [spatialPlaneOfPair_polar_norm point.1 point.2 radiusPositive.le]
      by_cases bounded : point.1 < 1
      · rw [indicator_of_mem target,indicator_of_mem (disk.mpr bounded),
          indicator_of_mem (show point ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi from ⟨⟨radiusPositive,bounded⟩,target.2⟩)]
      · have notDisk := (not_congr disk).mpr bounded
        have notProduct : point ∉ Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi := fun inside => bounded inside.1.2
        rw [indicator_of_mem target,indicator_of_notMem notDisk,indicator_of_notMem notProduct,mul_zero]
    · have notProduct : point ∉ Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi :=
        fun inside => target ⟨inside.1.1,inside.2⟩
      rw [indicator_of_notMem target,indicator_of_notMem notProduct]
  rw [← lintegral_indicator polarCoord.open_target.measurableSet,indicators,
    lintegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]

/-- A genuine polar norm integral implies Cartesian integrability;
finiteness is checked through the nonnegative integral, so no totalized
Bochner-integral identity can hide a failure of integrability. -/
theorem openDisk_integrable_of_polar {E : Type*} [NormedAddCommGroup E]
    (field : SpatialPlane → E)
    (measurable : AEStronglyMeasurable field (volume.restrict openUnitDisk))
    (polarIntegrable : IntegrableOn
      (fun point : ℝ × ℝ => point.1 * ‖field (spatialPlaneOfPair (polarCoord.symm point))‖)
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi)) :
    IntegrableOn field openUnitDisk := by
  refine ⟨measurable,?_⟩
  apply (hasFiniteIntegral_iff_norm field).mpr
  rw [openDisk_lintegral_eq_polar]
  have nonnegative : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi)]
      (fun point : ℝ × ℝ => point.1 * ‖field (spatialPlaneOfPair (polarCoord.symm point))‖) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with point inside
    exact mul_nonneg inside.1.1.le (norm_nonneg _)
  have finite := (hasFiniteIntegral_iff_ofReal nonnegative).mp polarIntegrable.hasFiniteIntegral
  have identity : (∫⁻ point : ℝ × ℝ in Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal point.1 * ENNReal.ofReal ‖field (spatialPlaneOfPair (polarCoord.symm point))‖) =
      ∫⁻ point : ℝ × ℝ in Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal (point.1 * ‖field (spatialPlaneOfPair (polarCoord.symm point))‖) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with point inside
    exact (ENNReal.ofReal_mul inside.1.1.le).symm
  rw [identity]
  exact finite

end Grad.WeightedAxisRemoval
