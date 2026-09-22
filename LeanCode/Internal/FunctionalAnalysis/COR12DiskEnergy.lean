import COR12OriginalGrade
import COR12TorusNormalization

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Grad.COR12Extension

open Grad.ClosedJets
open Grad.CartesianState
open Grad.DiskExtension.Operator
open Grad.FourierGrade

local instance : Fact (0 < (2 * Real.pi : ℝ)) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

theorem disk_volume_restrict_closed_eq_open :
    (volume : Measure SpatialPlane).restrict closedUnitDisk =
      volume.restrict openUnitDisk := by
  apply Measure.restrict_congr_set
  have outsideSphere : ∀ᵐ point : SpatialPlane ∂volume,
      point ∉ Metric.sphere (0 : SpatialPlane) 1 := by
    apply ae_iff.mpr
    have same : {point : SpatialPlane | ¬ point ∉ Metric.sphere (0 : SpatialPlane) 1} =
        Metric.sphere (0 : SpatialPlane) 1 := by
      apply Set.ext
      intro point
      exact not_not
    rw [same]
    exact Measure.addHaar_sphere (volume : Measure SpatialPlane) (0 : SpatialPlane) 1
  filter_upwards [outsideSphere] with point outside
  apply propext
  change ‖point‖ ≤ 1 ↔ ‖point‖ < 1
  have unequal : ‖point‖ ≠ 1 := by simpa [Metric.mem_sphere, dist_zero_right] using outside
  exact le_iff_lt_or_eq.trans (or_iff_left unequal)

theorem closedContinuous_radial_sq_integrable {dimension : ℕ}
    (field : C(ClosedDisk, ComplexEuclidean dimension)) :
    Integrable (fun point : SpatialPlane => ‖field (radialRetraction point)‖ ^ 2)
      (volume.restrict openUnitDisk) := by
  have continuousDensity : Continuous
      (fun point : SpatialPlane => ‖field (radialRetraction point)‖ ^ 2) :=
    (field.continuous.comp continuous_radialRetraction).norm.pow 2
  apply (integrable_const (‖field‖ ^ 2)).mono' continuousDensity.aestronglyMeasurable
  filter_upwards [] with point
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (field.norm_coe_le_norm _) 2

theorem closedContinuous_radial_sq_integral {dimension : ℕ}
    (field : C(ClosedDisk, ComplexEuclidean dimension)) :
    (∫ point : SpatialPlane, ‖field (radialRetraction point)‖ ^ 2
      ∂volume.restrict openUnitDisk) = ‖closedContinuousToDiskL2 field‖ ^ 2 := by
  rw [diskL2_norm_sq]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem openUnitDisk_isOpen.measurableSet,
    closedContinuousToDiskL2_ae field] with point member value
  rw [value, closedDiskLift, dif_pos (openDiskMembershipClosed point member)]
  have retraction : radialRetraction point =
      (⟨point, openDiskMembershipClosed point member⟩ : ClosedDisk) :=
    Subtype.ext (radialRetraction_val_of_mem point (openDiskMembershipClosed point member))
  rw [retraction]

def diskCoordinateEnergy {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : DiskCellMultiIndex) : ℝ :=
  ∫ cell : CellCircle, ∫ point : SpatialPlane,
    ‖closedDiskLift
      (fun diskPoint => closedDiskCellMultiDerivative field index (diskPoint, cell)) point‖ ^ 2
    ∂volume ∂cellProbabilityMeasure

def diskCoefficientCoordinateEnergy {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : DiskCellMultiIndex) : ℝ :=
  ∑' cell : ℤ, |(cell : ℝ)| ^ (2 * index.2) *
    ‖closedDerivativeL2 index.1 (diskCellFourierCoefficientJet field cell)‖ ^ 2

theorem diskCoefficientCoordinate_summable {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : DiskCellMultiIndex) :
    Summable (fun cell : ℤ => |(cell : ℝ)| ^ (2 * index.2) *
      ‖closedDerivativeL2 index.1 (diskCellFourierCoefficientJet field cell)‖ ^ 2) := by
  have source := diskCellFourierDerivativeL2_weighted_sq_summable field
    (cartesianMultiIndexWord index.1) index.2
  have source' : Summable (fun cell : ℤ => cellFrequency cell ^ (2 * index.2) *
      ‖closedDerivativeL2 index.1 (diskCellFourierCoefficientJet field cell)‖ ^ 2) := by
    apply source.congr
    intro cell
    change _ = cellFrequency cell ^ (2 * index.2) *
      ‖closedContinuousToDiskL2
        (closedMultiDerivative (diskCellFourierCoefficientJet field cell) index.1)‖ ^ 2
    rw [closedMultiDerivative_diskCellFourierCoefficientJet]
  exact Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun cell => mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (abs_nonneg _) (cell_abs_le_frequency cell) _) (sq_nonneg _)) source'

def diskCoefficientDensity {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : DiskCellMultiIndex)
    (cell : ℤ) (point : SpatialPlane) : ℝ :=
  |(cell : ℝ)| ^ (2 * index.2) *
    ‖closedMultiDerivative (diskCellFourierCoefficientJet field cell) index.1
      (radialRetraction point)‖ ^ 2

theorem diskCoefficientDensity_integrable {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : DiskCellMultiIndex) (cell : ℤ) :
    Integrable (diskCoefficientDensity field index cell) (volume.restrict openUnitDisk) :=
  (closedContinuous_radial_sq_integrable
    (closedMultiDerivative (diskCellFourierCoefficientJet field cell) index.1)).const_mul _

theorem diskCoefficientDensity_integral {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : DiskCellMultiIndex) (cell : ℤ) :
    (∫ point : SpatialPlane, diskCoefficientDensity field index cell point
      ∂volume.restrict openUnitDisk) =
      |(cell : ℝ)| ^ (2 * index.2) *
        ‖closedDerivativeL2 index.1 (diskCellFourierCoefficientJet field cell)‖ ^ 2 := by
  unfold diskCoefficientDensity
  rw [integral_const_mul, closedContinuous_radial_sq_integral]
  rfl

theorem diskCoordinateEnergy_parseval {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : DiskCellMultiIndex) :
    (2 * Real.pi) * diskCoordinateEnergy field index =
      diskCoefficientCoordinateEnergy field index := by
  have jointContinuous : Continuous
      (fun pair : SpatialPlane × CellCircle =>
        ‖closedDiskCellMultiDerivative field index (radialRetraction pair.1, pair.2)‖ ^ 2) := by
    exact (((closedDiskCellMultiDerivative field index).continuous.comp
      ((continuous_radialRetraction.comp continuous_fst).prodMk continuous_snd)).norm).pow 2
  have jointIntegrable : Integrable
      (fun pair : SpatialPlane × CellCircle =>
        ‖closedDiskCellMultiDerivative field index (radialRetraction pair.1, pair.2)‖ ^ 2)
      ((volume.restrict openUnitDisk).prod AddCircle.haarAddCircle) := by
    apply (integrable_const (‖closedDiskCellMultiDerivative field index‖ ^ 2)).mono'
      jointContinuous.aestronglyMeasurable
    filter_upwards [] with pair
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((closedDiskCellMultiDerivative field index).norm_coe_le_norm _) 2
  have normIntegralSummable : Summable (fun cell : ℤ =>
      ∫ point : SpatialPlane, ‖diskCoefficientDensity field index cell point‖
        ∂volume.restrict openUnitDisk) := by
    apply (diskCoefficientCoordinate_summable field index).congr
    intro cell
    rw [← diskCoefficientDensity_integral]
    apply integral_congr_ae
    filter_upwards [] with point
    exact (Real.norm_of_nonneg (by unfold diskCoefficientDensity; positivity)).symm
  calc
    (2 * Real.pi) * diskCoordinateEnergy field index =
        ∫ cell : CellCircle, ∫ point : SpatialPlane,
          ‖closedDiskCellMultiDerivative field index (radialRetraction point, cell)‖ ^ 2
            ∂volume.restrict openUnitDisk ∂AddCircle.haarAddCircle := by
      unfold diskCoordinateEnergy
      simp only [cellProbabilityMeasure, integral_smul_measure, ENNReal.toReal_inv,
        ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * Real.pi), smul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), one_mul]
      apply integral_congr_ae
      filter_upwards [] with cell
      rw [← closedIndexSquaredDensity_integral_eq, disk_volume_restrict_closed_eq_open]
      rfl
    _ = ∫ point : SpatialPlane, ∫ cell : CellCircle,
        ‖closedDiskCellMultiDerivative field index (radialRetraction point, cell)‖ ^ 2
          ∂AddCircle.haarAddCircle ∂volume.restrict openUnitDisk :=
      (integral_integral_swap jointIntegrable).symm
    _ = ∫ point : SpatialPlane, ∑' cell : ℤ,
        diskCoefficientDensity field index cell point ∂volume.restrict openUnitDisk := by
      apply integral_congr_ae
      filter_upwards [] with point
      exact diskDerivativeCellSlice_parseval_coefficient field index.1 index.2
        (radialRetraction point)
    _ = ∑' cell : ℤ, ∫ point : SpatialPlane,
        diskCoefficientDensity field index cell point ∂volume.restrict openUnitDisk :=
      (integral_tsum_of_summable_integral_norm
        (diskCoefficientDensity_integrable field index) normIntegralSummable).symm
    _ = diskCoefficientCoordinateEnergy field index := by
      exact tsum_congr (diskCoefficientDensity_integral field index)

theorem diskDerivativeEnergy_parseval {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (grade : ℕ) :
    (2 * Real.pi) * diskDerivativeEnergy grade field =
      ∑ index ∈ fourierMultiIndices grade, diskCoefficientCoordinateEnergy field index := by
  unfold diskDerivativeEnergy
  rw [diskCellMultiIndices_eq_fourierMultiIndices, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun index _ => diskCoordinateEnergy_parseval field index)

end Grad.COR12Extension
