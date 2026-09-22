import P0910Restriction

noncomputable section

open Set
open scoped BigOperators Topology

namespace Grad.DiskExtension.Operator

open Grad.ClosedJets

theorem closedDiskLift_add {dimension : ℕ}
    (first second : ContinuousMap DiskCellDomain (ComplexEuclidean dimension))
    (point : SpatialPlane) (cell : CellCircle) :
    closedDiskLift (fun diskPoint =>
      first (diskPoint, cell) + second (diskPoint, cell)) point =
      closedDiskLift (fun diskPoint => first (diskPoint, cell)) point +
        closedDiskLift (fun diskPoint => second (diskPoint, cell)) point := by
  classical
  by_cases membership : point ∈ closedUnitDisk <;>
    simp [closedDiskLift, membership]

theorem closedDiskLift_smul {dimension : ℕ} (scalar : ℂ)
    (value : ContinuousMap DiskCellDomain (ComplexEuclidean dimension))
    (point : SpatialPlane) (cell : CellCircle) :
    closedDiskLift (fun diskPoint => scalar • value (diskPoint, cell)) point =
      scalar • closedDiskLift (fun diskPoint => value (diskPoint, cell)) point := by
  classical
  by_cases membership : point ∈ closedUnitDisk <;>
    simp [closedDiskLift, membership]

theorem exteriorSummand_add {dimension : ℕ}
    (first second : DiskCellClosedJet dimension)
    (index : ℕ) (point : SpatialPlane) (cell : CellCircle) :
    exteriorSummandFromValue (diskCellJetAddValue first second) index point cell =
      exteriorSummandFromValue first.value index point cell +
        exteriorSummandFromValue second.value index point cell := by
  classical
  by_cases membership : reflectedPoint index point ∈ closedUnitDisk
  · simp [exteriorSummandFromValue, closedDiskLift, membership,
      diskCellJetAddValue, smul_add]
  · simp [exteriorSummandFromValue, closedDiskLift, membership]

theorem exteriorSummand_smul {dimension : ℕ} (scalar : ℂ)
    (field : DiskCellClosedJet dimension)
    (index : ℕ) (point : SpatialPlane) (cell : CellCircle) :
    exteriorSummandFromValue (diskCellJetSmulValue scalar field) index point cell =
      scalar • exteriorSummandFromValue field.value index point cell := by
  classical
  by_cases membership : reflectedPoint index point ∈ closedUnitDisk
  · simp only [exteriorSummandFromValue, closedDiskLift, dif_pos membership,
      diskCellJetSmulValue, ContinuousMap.coe_mk]
    rw [smul_comm]
  · simp [exteriorSummandFromValue, closedDiskLift, membership]

theorem exteriorSeries_add {dimension : ℕ}
    (first second : DiskCellClosedJet dimension)
    (point : SpatialPlane) (cell : CellCircle) :
    exteriorSeriesFromValue (diskCellJetAddValue first second) point cell =
      exteriorSeriesFromValue first.value point cell +
        exteriorSeriesFromValue second.value point cell := by
  unfold exteriorSeriesFromValue
  simp_rw [exteriorSummand_add]
  exact (exteriorSummand_summable first.value point cell).tsum_add
    (exteriorSummand_summable second.value point cell)

theorem exteriorSeries_smul {dimension : ℕ} (scalar : ℂ)
    (field : DiskCellClosedJet dimension)
    (point : SpatialPlane) (cell : CellCircle) :
    exteriorSeriesFromValue (diskCellJetSmulValue scalar field) point cell =
      scalar • exteriorSeriesFromValue field.value point cell := by
  unfold exteriorSeriesFromValue
  simp_rw [exteriorSummand_smul]
  exact Summable.tsum_const_smul scalar
    (exteriorSummand_summable field.value point cell)

theorem ambientExtension_add {dimension : ℕ}
    (first second : DiskCellClosedJet dimension)
    (point : SpatialPlane) (cell : CellCircle) :
    ambientExtensionFromValue (diskCellJetAddValue first second) point cell =
      ambientExtensionFromValue first.value point cell +
        ambientExtensionFromValue second.value point cell := by
  classical
  by_cases membership : point ∈ closedUnitDisk
  · simp [ambientExtensionFromValue, membership, diskCellJetAddValue]
  · simp only [ambientExtensionFromValue, dif_neg membership]
    exact exteriorSeries_add first second point cell

theorem ambientExtension_smul {dimension : ℕ} (scalar : ℂ)
    (field : DiskCellClosedJet dimension)
    (point : SpatialPlane) (cell : CellCircle) :
    ambientExtensionFromValue (diskCellJetSmulValue scalar field) point cell =
      scalar • ambientExtensionFromValue field.value point cell := by
  classical
  by_cases membership : point ∈ closedUnitDisk
  · simp [ambientExtensionFromValue, membership, diskCellJetSmulValue]
  · simp only [ambientExtensionFromValue, dif_neg membership]
    exact exteriorSeries_smul scalar field point cell

theorem periodizedExtension_add {dimension : ℕ}
    (first second : DiskCellClosedJet dimension) (point : TorusCellDomain) :
    periodizedExtensionFromValue (diskCellJetAddValue first second) point =
      periodizedExtensionFromValue first.value point +
        periodizedExtensionFromValue second.value point := by
  exact ambientExtension_add first second (spatialTorusRepresentative point.1) point.2

theorem periodizedExtension_smul {dimension : ℕ} (scalar : ℂ)
    (field : DiskCellClosedJet dimension) (point : TorusCellDomain) :
    periodizedExtensionFromValue (diskCellJetSmulValue scalar field) point =
      scalar • periodizedExtensionFromValue field.value point := by
  exact ambientExtension_smul scalar field (spatialTorusRepresentative point.1) point.2

theorem closedDisk_coordinate_mem_Ico (point : ClosedDisk) (coordinate : Fin 2) :
    point.val coordinate ∈ Set.Ico (-2 : ℝ) (-2 + 4) := by
  have coordinateBound : |point.val coordinate| ≤ ‖point.val‖ := by
    have squareBound : (point.val coordinate) ^ 2 ≤ ‖point.val‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.single_le_sum (fun index _ => sq_nonneg (point.val index))
        (Finset.mem_univ coordinate)
    nlinarith [sq_abs (point.val coordinate), abs_nonneg (point.val coordinate),
      norm_nonneg point.val]
  have diskBound : ‖point.val‖ ≤ 1 := point.property
  constructor <;> norm_num <;> nlinarith [neg_abs_le (point.val coordinate),
    le_abs_self (point.val coordinate)]

theorem spatialTorusRepresentative_diskToTorus (point : DiskCellDomain) :
    spatialTorusRepresentative (diskToTorus point).1 = point.1.val := by
  ext coordinate
  fin_cases coordinate
  · change ((AddCircle.equivIco (4 : ℝ) (-2) (point.1.val 0 : SpatialCircle)).val) =
      point.1.val 0
    rw [AddCircle.equivIco_coe_eq (closedDisk_coordinate_mem_Ico point.1 0)]
  · change ((AddCircle.equivIco (4 : ℝ) (-2) (point.1.val 1 : SpatialCircle)).val) =
      point.1.val 1
    rw [AddCircle.equivIco_coe_eq (closedDisk_coordinate_mem_Ico point.1 1)]

theorem periodizedExtension_restricts {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : DiskCellDomain) :
    periodizedExtensionFromValue field.value (diskToTorus point) = field.value point := by
  rw [periodizedExtensionFromValue, spatialTorusRepresentative_diskToTorus]
  exact ambientExtension_inside field.value point.1.val point.1.property point.2

end Grad.DiskExtension.Operator
