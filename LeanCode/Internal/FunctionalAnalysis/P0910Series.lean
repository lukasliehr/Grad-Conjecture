import P0910Plateau
import Mathlib.Topology.ContinuousMap.Compact

noncomputable section

open Set
open scoped BigOperators Topology

namespace Grad.DiskExtension.Operator

open Grad.ClosedJets
open Grad.DiskExtension.Seeley

local instance closedDiskCompactSpace : CompactSpace ClosedDisk := by
  rw [← isCompact_iff_compactSpace, closedUnitDisk_eq_closedBall]
  exact isCompact_closedBall (0 : SpatialPlane) 1

theorem closedDiskLift_norm_le {dimension : ℕ}
    (value : ContinuousMap DiskCellDomain (ComplexEuclidean dimension))
    (point : SpatialPlane) (cell : CellCircle) :
    ‖closedDiskLift (fun diskPoint => value (diskPoint, cell)) point‖ ≤ ‖value‖ := by
  classical
  by_cases membership : point ∈ closedUnitDisk
  · rw [closedDiskLift, dif_pos membership]
    exact value.norm_coe_le_norm (⟨point, membership⟩, cell)
  · rw [closedDiskLift, dif_neg membership, norm_zero]
    exact norm_nonneg value

theorem exteriorSummand_norm_le {dimension : ℕ}
    (value : ContinuousMap DiskCellDomain (ComplexEuclidean dimension))
    (index : ℕ) (point : SpatialPlane) (cell : CellCircle) :
    ‖exteriorSummandFromValue value index point cell‖ ≤
      |coefficient index| * ‖value‖ := by
  rw [exteriorSummandFromValue, norm_smul]
  have cutoff_nonnegative :=
    (plateauCutoff_range (node index * (‖point‖ - 1))).1
  have cutoff_le :=
    (plateauCutoff_range (node index * (‖point‖ - 1))).2
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg cutoff_nonnegative]
  calc
    |coefficient index| * plateauCutoff (node index * (‖point‖ - 1)) *
        ‖closedDiskLift (fun diskPoint => value (diskPoint, cell))
          (reflectedPoint index point)‖
        ≤ |coefficient index| * 1 * ‖value‖ := by
          gcongr
          exact closedDiskLift_norm_le value (reflectedPoint index point) cell
    _ = |coefficient index| * ‖value‖ := by ring

theorem coefficient_absolute_summable : Summable (fun index => |coefficient index|) := by
  simpa only [pow_zero, mul_one] using coefficient_absolute_moment_summable 0

theorem exteriorSummand_summable {dimension : ℕ}
    (value : ContinuousMap DiskCellDomain (ComplexEuclidean dimension))
    (point : SpatialPlane) (cell : CellCircle) :
    Summable (fun index => exteriorSummandFromValue value index point cell) := by
  apply (coefficient_absolute_summable.mul_right ‖value‖).of_norm_bounded
  exact fun index => exteriorSummand_norm_le value index point cell

theorem exteriorSummand_zero_of_support {dimension : ℕ}
    (value : ContinuousMap DiskCellDomain (ComplexEuclidean dimension))
    (index : ℕ) (point : SpatialPlane) (cell : CellCircle)
    (outside : outerSupportRadius ≤ ‖point‖) :
    exteriorSummandFromValue value index point cell = 0 := by
  have radial : cutoffSupportWidth ≤ node index * (‖point‖ - 1) := by
    rw [collar_constants.2.2.1]
    rw [collar_constants.2.2.2.2] at outside
    have nodeBound := node_one_le index
    nlinarith [node_positive index]
  simp [exteriorSummandFromValue, plateauCutoff_zero _ radial]

theorem exteriorSeries_zero_of_support {dimension : ℕ}
    (value : ContinuousMap DiskCellDomain (ComplexEuclidean dimension))
    (point : SpatialPlane) (cell : CellCircle)
    (outside : outerSupportRadius ≤ ‖point‖) :
    exteriorSeriesFromValue value point cell = 0 := by
  unfold exteriorSeriesFromValue
  have terms : (fun index => exteriorSummandFromValue value index point cell) = 0 := by
    funext index
    exact exteriorSummand_zero_of_support value index point cell outside
  rw [terms]
  exact tsum_zero

theorem ambientExtension_inside {dimension : ℕ}
    (value : ContinuousMap DiskCellDomain (ComplexEuclidean dimension))
    (point : SpatialPlane) (membership : point ∈ closedUnitDisk) (cell : CellCircle) :
    ambientExtensionFromValue value point cell = value (⟨point, membership⟩, cell) := by
  rw [ambientExtensionFromValue, dif_pos membership]

theorem ambientExtension_zero_of_support {dimension : ℕ}
    (value : ContinuousMap DiskCellDomain (ComplexEuclidean dimension))
    (point : SpatialPlane) (cell : CellCircle)
    (outside : outerSupportRadius ≤ ‖point‖) :
    ambientExtensionFromValue value point cell = 0 := by
  have not_disk : point ∉ closedUnitDisk := by
    rw [collar_constants.2.2.2.2] at outside
    change ¬‖point‖ ≤ 1
    linarith
  rw [ambientExtensionFromValue, dif_neg not_disk]
  exact exteriorSeries_zero_of_support value point cell outside

theorem ambientExtension_support_subset {dimension : ℕ}
    (value : ContinuousMap DiskCellDomain (ComplexEuclidean dimension))
    (cell : CellCircle) :
    Function.support (fun point => ambientExtensionFromValue value point cell) ⊆
      Metric.ball (0 : SpatialPlane) 2 := by
  intro point nonzero
  rw [Metric.mem_ball, dist_zero_right]
  by_contra outside
  have radiusOutside : outerSupportRadius ≤ ‖point‖ := by
    rw [collar_constants.2.2.2.2]
    linarith
  exact nonzero (ambientExtension_zero_of_support value point cell radiusOutside)

theorem closedBall_two_subset_openPeriodSquare :
    Metric.closedBall (0 : SpatialPlane) outerSupportRadius ⊆ openPeriodSquare := by
  intro point membership
  rw [Metric.mem_closedBall, dist_zero_right] at membership
  rw [collar_constants.2.2.2.2] at membership
  have coordinateBound (coordinate : Fin 2) : |point coordinate| ≤ ‖point‖ := by
    have squareBound : (point coordinate) ^ 2 ≤ ‖point‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.single_le_sum (fun index _ => sq_nonneg (point index))
        (Finset.mem_univ coordinate)
    nlinarith [sq_abs (point coordinate), abs_nonneg (point coordinate), norm_nonneg point]
  have firstBound := coordinateBound 0
  have secondBound := coordinateBound 1
  rw [openPeriodSquare]
  change -2 < point 0 ∧ point 0 < 2 ∧ -2 < point 1 ∧ point 1 < 2
  constructor
  · linarith [neg_abs_le (point 0)]
  constructor
  · linarith [le_abs_self (point 0)]
  constructor
  · linarith [neg_abs_le (point 1)]
  · linarith [le_abs_self (point 1)]

theorem ambientExtension_tsupport_subset {dimension : ℕ}
    (value : ContinuousMap DiskCellDomain (ComplexEuclidean dimension))
    (cell : CellCircle) :
    tsupport (fun point => ambientExtensionFromValue value point cell) ⊆ openPeriodSquare := by
  apply (show tsupport (fun point => ambientExtensionFromValue value point cell) ⊆
      Metric.closedBall (0 : SpatialPlane) outerSupportRadius from ?_).trans
    closedBall_two_subset_openPeriodSquare
  rw [tsupport]
  apply closure_minimal
  · intro point nonzero
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra outside
    exact nonzero (ambientExtension_zero_of_support value point cell (le_of_not_ge outside))
  · exact Metric.isClosed_closedBall

end Grad.DiskExtension.Operator
