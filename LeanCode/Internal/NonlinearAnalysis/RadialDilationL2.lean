import RadialDilationJet
import ProductDiskL2
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace Grad.NonlinearRadial

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct

def dilationDomain (scale : ℝ) : Set SpatialPlane :=
  (fun point : SpatialPlane => scale • point) ⁻¹' openUnitDisk

theorem disk_subset_dilationDomain {scale : ℝ} (positive : 0 < scale) (bounded : scale ≤ 1) :
    openUnitDisk ⊆ dilationDomain scale := by
  intro point inside
  change ‖scale • point‖ < 1
  rw [norm_smul, Real.norm_of_nonneg positive.le]
  exact (mul_le_of_le_one_left (norm_nonneg point) bounded).trans_lt inside

theorem dilation_measurePreserving {scale : ℝ} (positive : 0 < scale) :
    MeasurePreserving (fun point : SpatialPlane => scale • point)
      (volume.restrict (dilationDomain scale))
      (ENNReal.ofReal ((scale ^ 2)⁻¹) • volume.restrict openUnitDisk) := by
  refine ⟨measurable_const_smul scale, ?_⟩
  rw [dilationDomain, ← Measure.restrict_map (measurable_const_smul scale)
    openUnitDisk_isOpen.measurableSet]
  have raw : Measure.map (fun point : SpatialPlane => scale • point) volume =
      ENNReal.ofReal ((scale ^ 2)⁻¹) • volume := by
    simpa only [SpatialPlane, finrank_euclideanSpace_fin,
      abs_of_nonneg (inv_nonneg.mpr (sq_nonneg scale))] using
      (Measure.map_addHaar_smul (volume : Measure SpatialPlane) positive.ne')
  rw [raw, Measure.restrict_smul]

theorem closedValueL2_norm_sq {dimension : ℕ} (field : C(ClosedDisk, ComplexEuclidean dimension)) :
    ‖closedContinuousToDiskL2 field‖ ^ 2 =
      ∫ point : SpatialPlane in openUnitDisk, ‖field (ambientClosedDisk point)‖ ^ 2 := by
  rw [← closedMapL2_eq_original, diskL2_norm_sq]
  apply integral_congr_ae
  filter_upwards [closedMapL2_ae field] with point equality
  rw [equality]

theorem closedValueL2_dilation_bound {dimension : ℕ} {scale : ℝ}
    (positive : 0 < scale) (bounded : scale ≤ 1)
    (field : C(ClosedDisk, ComplexEuclidean dimension)) :
    ‖closedContinuousToDiskL2 (field.comp (dilationClosedMap scale positive.le bounded))‖ ≤
      scale⁻¹ * ‖closedContinuousToDiskL2 field‖ := by
  let function : SpatialPlane → ℝ := fun point => ‖field (ambientClosedDisk point)‖ ^ 2
  have continuousFunction : Continuous function :=
    (field.continuous.comp continuous_ambientClosedDisk).norm.pow 2
  have integrableFunction : Integrable function (volume.restrict openUnitDisk) := by
    exact (closedMapMemL2 field).norm.integrable_sq
  have scaledIntegrable : Integrable function
      (ENNReal.ofReal ((scale ^ 2)⁻¹) • volume.restrict openUnitDisk) :=
    integrableFunction.smul_measure ENNReal.ofReal_ne_top
  have pulledIntegrable : Integrable (fun point : SpatialPlane => function (scale • point))
      (volume.restrict (dilationDomain scale)) :=
    ((dilation_measurePreserving positive).integrable_comp
      continuousFunction.aestronglyMeasurable).mpr scaledIntegrable
  have embedding : MeasurableEmbedding (fun point : SpatialPlane => scale • point) :=
    (Homeomorph.smul (α := SpatialPlane) (isUnit_iff_ne_zero.2 positive.ne').unit).measurableEmbedding
  have changeVariables :
      (∫ point in dilationDomain scale, function (scale • point)) =
        (scale ^ 2)⁻¹ * ∫ point in openUnitDisk, function point := by
    rw [(dilation_measurePreserving positive).integral_comp embedding function,
      integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr (sq_nonneg scale))]
    rfl
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr positive.le) (norm_nonneg _))).mp
  rw [mul_pow, inv_pow, closedValueL2_norm_sq, closedValueL2_norm_sq]
  calc
    _ = ∫ point in openUnitDisk, function (scale • point) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point pointIn
      have sourceClosed := openDiskMembershipClosed point pointIn
      have scaledClosed := dilation_mem_closed positive.le bounded ⟨point, sourceClosed⟩
      have points : dilationClosedMap scale positive.le bounded (ambientClosedDisk point) =
          ambientClosedDisk (scale • point) := by
        apply Subtype.ext
        change scale • (ambientClosedDisk point).val = (ambientClosedDisk (scale • point)).val
        rw [ambientClosedDisk_val_of_mem sourceClosed, ambientClosedDisk_val_of_mem scaledClosed]
      simp only [ContinuousMap.comp_apply, points, function]
    _ ≤ ∫ point in dilationDomain scale, function (scale • point) := by
      apply integral_mono_measure (Measure.restrict_mono
        (disk_subset_dilationDomain positive bounded) le_rfl)
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) pulledIntegrable
    _ = _ := changeVariables

end Grad.NonlinearRadial
