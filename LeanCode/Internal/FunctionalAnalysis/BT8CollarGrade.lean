import BT7CollarMeasure

noncomputable section

set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.BoundaryTrace

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.DiskExtension.Operator

def cartesianDensityGlobal {dimension : ℕ} (frequency : ℝ) (grade : ℕ)
    (field : ClosedJet dimension) (point : SpatialPlane) : ℝ :=
  cartesianPointDensity frequency grade field (ambientClosedDisk point)

theorem cartesianDensityGlobal_continuous {dimension : ℕ} (frequency : ℝ) (grade : ℕ)
    (field : ClosedJet dimension) : Continuous (cartesianDensityGlobal frequency grade field) := by
  apply continuous_finsetSum
  intro index _
  exact continuous_const.mul (((closedMultiDerivative field index.toCartesian).continuous.comp
    continuous_ambientClosedDisk).norm.pow 2)

theorem cartesianDensityGlobal_closed {dimension : ℕ} (frequency : ℝ) (grade : ℕ)
    (field : ClosedJet dimension) (point : ClosedDisk) :
    cartesianDensityGlobal frequency grade field point.val = cartesianPointDensity frequency grade field point := by
  have ambientEquality : ambientClosedDisk point.val = point := by
    apply Subtype.ext
    exact ambientClosedDisk_val_of_mem point.property
  rw [cartesianDensityGlobal, ambientEquality]

theorem closedDerivative_density_integral {dimension : ℕ} (field : ClosedJet dimension)
    (index : CartesianMultiIndex) :
    (∫ point in closedUnitDisk, ‖closedMultiDerivative field index (ambientClosedDisk point)‖ ^ 2) =
      ‖closedDerivativeL2 index field‖ ^ 2 := by
  rw [Measure.restrict_congr_set closedUnitDisk_ae_openUnitDisk, closedDerivativeL2_norm_sq]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point inside
  rw [closedDiskLift, dif_pos (openDiskMembershipClosed point inside)]
  have ambientEquality : ambientClosedDisk point =
      (⟨point, openDiskMembershipClosed point inside⟩ : ClosedDisk) := by
    apply Subtype.ext
    exact ambientClosedDisk_val_of_mem (openDiskMembershipClosed point inside)
  rw [ambientEquality]

theorem cartesianDensityGlobal_integral {dimension : ℕ} (frequency : ℝ) (grade : ℕ)
    (field : ClosedJet dimension) :
    (∫ point in closedUnitDisk, cartesianDensityGlobal frequency grade field point) =
      ∑ index : GradeMultiIndex grade, frequency ^ (2 * (grade - cartesianOrder index.toCartesian)) *
        ‖closedDerivativeL2 index.toCartesian field‖ ^ 2 := by
  unfold cartesianDensityGlobal cartesianPointDensity
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro index _
    rw [integral_const_mul, closedDerivative_density_integral]
  · intro index _
    have compactDisk : IsCompact closedUnitDisk := by
      rw [closedUnitDisk_eq_closedBall]
      exact isCompact_closedBall _ _
    exact (continuous_const.mul (((closedMultiDerivative field index.toCartesian).continuous.comp
      continuous_ambientClosedDisk).norm.pow 2)).continuousOn.integrableOn_compact compactDisk

theorem cartesianDensityGlobal_integral_original {dimension grade : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension) :
    (∫ point in closedUnitDisk,
      cartesianDensityGlobal (cellFrequency cell) grade (phaseWeightedJet parameters cell field) point) =
        ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ^ 2 := by
  rw [cartesianDensityGlobal_integral, cellGradeRow_norm_sq]
  rfl

def collarIntegral (function : ℝ × ℝ → ℝ) : ℝ :=
  ∫ angle in Ioo (-Real.pi) Real.pi, ∫ time in (0 : ℝ)..(1 / 4 : ℝ), function (time, angle)

theorem collarIntegral_mono (first second : ℝ × ℝ → ℝ)
    (firstContinuous : Continuous first) (secondContinuous : Continuous second)
    (bound : ∀ point ∈ collarRectangle, first point ≤ second point) :
    collarIntegral first ≤ collarIntegral second := by
  apply integral_mono_ae
  · exact ((timeIntegral_continuous first firstContinuous 0 (1 / 4) (by norm_num)).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  · exact ((timeIntegral_continuous second secondContinuous 0 (1 / 4) (by norm_num)).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with angle angleIn
    apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1 / 4)
    · exact (firstContinuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    · exact (secondContinuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    · intro time timeIn
      exact bound (time, angle) ⟨timeIn, ⟨angleIn.1.le, angleIn.2.le⟩⟩

theorem collarIntegral_const_mul (scalar : ℝ) (function : ℝ × ℝ → ℝ) :
    collarIntegral (fun point => scalar * function point) = scalar * collarIntegral function := by
  unfold collarIntegral
  simp only [intervalIntegral.integral_const_mul, integral_const_mul]

def collarOrderConstant (order : ℕ) : ℝ :=
  collarDerivativeConstant order order ^ 2 * (order + 1 : ℝ) * planarTensorConstant order

theorem collarOrderConstant_nonnegative (order : ℕ) : 0 ≤ collarOrderConstant order := by
  have tensorNonnegative : 0 ≤ planarTensorConstant order := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  unfold collarOrderConstant
  positivity

theorem weighted_collar_integral_le_original {dimension grade order : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension) (upper : order ≤ grade) :
    cellFrequency cell ^ (2 * (grade - order)) * collarIntegral (fun point =>
      ‖iteratedFDeriv ℝ order (collarField (smoothClosedExtension (phaseWeightedJet parameters cell field))) point‖ ^ 2) ≤
      ((4 / 3 : ℝ) * collarOrderConstant order) * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ^ 2 := by
  let weighted := phaseWeightedJet parameters cell field
  let density := cartesianDensityGlobal (cellFrequency cell) grade weighted
  have densityContinuous : Continuous density := cartesianDensityGlobal_continuous _ _ _
  have derivativeContinuous : Continuous (fun point =>
      ‖iteratedFDeriv ℝ order (collarField (smoothClosedExtension weighted)) point‖ ^ 2) :=
    (((collarField_smooth (smoothClosedExtension_smooth weighted)).continuous_iteratedFDeriv
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).norm.pow 2)
  have pointwise : ∀ point ∈ collarRectangle,
      cellFrequency cell ^ (2 * (grade - order)) *
        ‖iteratedFDeriv ℝ order (collarField (smoothClosedExtension weighted)) point‖ ^ 2 ≤
      collarOrderConstant order * density (collarPlane point) := by
    intro point inside
    have raw := weighted_collarDerivative_sq_le_density (cellFrequency cell)
      (cellFrequency_one_le cell) upper weighted point inside
    apply raw.trans_eq
    exact congrArg (fun value => collarOrderConstant order * value)
      (cartesianDensityGlobal_closed (cellFrequency cell) grade weighted
        ⟨collarPlane point, (collarPlane_radius inside).2⟩).symm
  have comparison := collarIntegral_mono
    (fun point => cellFrequency cell ^ (2 * (grade - order)) *
      ‖iteratedFDeriv ℝ order (collarField (smoothClosedExtension weighted)) point‖ ^ 2)
    (fun point => collarOrderConstant order * density (collarPlane point))
    (continuous_const.mul derivativeContinuous)
    (continuous_const.mul (densityContinuous.comp collarPlane_smooth.continuous)) pointwise
  rw [collarIntegral_const_mul, collarIntegral_const_mul] at comparison
  have polarBound := collar_integral_le_disk density densityContinuous (fun point =>
    cartesianPointDensity_nonnegative _ (cellFrequency_pos cell).le _ _ _)
  have diskIntegral : (∫ point in closedUnitDisk, density point) =
      ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ^ 2 :=
    cartesianDensityGlobal_integral_original parameters cell field
  rw [diskIntegral] at polarBound
  exact comparison.trans (by
    simpa only [collarIntegral, mul_assoc, mul_left_comm (collarOrderConstant order)] using
      mul_le_mul_of_nonneg_left polarBound (collarOrderConstant_nonnegative order))

end Grad.BoundaryTrace
