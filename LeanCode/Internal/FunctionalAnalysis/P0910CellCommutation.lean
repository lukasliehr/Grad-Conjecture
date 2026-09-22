import P0910OperatorCore
import Mathlib.Analysis.Calculus.TaylorIntegral

noncomputable section

open Filter Set
open scoped BigOperators ContDiff Topology

namespace Grad.DiskExtension.Operator

open Grad.ClosedJets
open Grad.DiskExtension.Seeley

theorem iteratedDeriv_comp_add_smul_eq_iteratedFDeriv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (function : E → F)
    (base direction : E) (order : ℕ) (parameter : ℝ) :
    (∀ scale : ℝ, ContDiffAt ℝ ∞ function (base + scale • direction)) →
    iteratedDeriv order (fun scale => function (base + scale • direction)) parameter =
      iteratedFDeriv ℝ order function (base + parameter • direction)
        (fun _ => direction) := by
  intro smooth
  induction order generalizing parameter with
  | zero => simp [iteratedDeriv_zero]
  | succ order induction =>
      rw [iteratedDeriv_succ]
      have functionEquality :
          (fun scale : ℝ => iteratedDeriv order
            (fun inner : ℝ => function (base + inner • direction)) scale) =
          (fun scale : ℝ => iteratedFDeriv ℝ order function
            (base + scale • direction) (fun _ => direction)) := by
        funext scale
        exact induction scale
      change deriv (fun scale : ℝ => iteratedDeriv order
        (fun inner : ℝ => function (base + inner • direction)) scale) parameter = _
      rw [functionEquality]
      exact ContDiffAt.deriv_fderiv_add_smul
        (𝕜 := ℝ) (f := function) (x := base) (y := direction)
        (t := parameter) ((smooth parameter).of_le (WithTop.coe_le_coe.mpr
          (show (order + 1 : ℕ∞) ≤ ⊤ from le_top)))

theorem planarPart_add_smul_cellBasis (point : SpatialCell) (scale : ℝ) :
    planarPart (point + scale • spatialCellBasis 2) = planarPart point := by
  ext coordinate
  fin_cases coordinate <;> simp [planarPart, spatialCellBasis]

theorem cellCoordinate_add_smul_cellBasis (point : SpatialCell) (scale : ℝ) :
    (point + scale • spatialCellBasis 2) 2 = point 2 + scale := by
  simp [spatialCellBasis]

theorem reflectedSpatialCell_add_smul_cellBasis (index : ℕ)
    (point : SpatialCell) (scale : ℝ) :
    reflectedSpatialCell index (point + scale • spatialCellBasis 2) =
      reflectedSpatialCell index point + scale • spatialCellBasis 2 := by
  ext coordinate
  fin_cases coordinate
  · change reflectedPoint index
      (planarPart (point + scale • spatialCellBasis 2)) 0 = _
    rw [planarPart_add_smul_cellBasis]
    simp [reflectedSpatialCell, assembleSpatialCell, spatialCellBasis]
  · change reflectedPoint index
      (planarPart (point + scale • spatialCellBasis 2)) 1 = _
    rw [planarPart_add_smul_cellBasis]
    simp [reflectedSpatialCell, assembleSpatialCell, spatialCellBasis]
  · simp [reflectedSpatialCell, assembleSpatialCell, spatialCellBasis]

theorem pureCellMixedDerivative_eq_iteratedDeriv_line
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (function : SpatialCell → F) (point : SpatialCell) (order : ℕ)
    (smoothAlong : ∀ scale : ℝ, ContDiffAt ℝ ∞ function
      (point + scale • spatialCellBasis 2)) :
    mixedCartesianDerivative order (pureCellWord order) function point =
      iteratedDeriv order
        (fun scale : ℝ => function (point + scale • spatialCellBasis 2)) 0 := by
  rw [mixedCartesianDerivative,
    iteratedDeriv_comp_add_smul_eq_iteratedFDeriv
      function point (spatialCellBasis 2) order 0 smoothAlong]
  simp [pureCellWord]

theorem diskCellLift_cellLine_contDiff
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (point : SpatialCell) (membership : point ∈ openUnitCylinder) :
    ContDiff ℝ ∞ (fun scale : ℝ =>
      diskCellLift field.value (point + scale • spatialCellBasis 2)) := by
  rw [contDiff_iff_contDiffAt]
  intro scale
  have shiftedMembership :
      point + scale • spatialCellBasis 2 ∈ openUnitCylinder := by
    change ‖planarPart (point + scale • spatialCellBasis 2)‖ < 1
    rw [planarPart_add_smul_cellBasis]
    exact membership
  have outerSmooth := (field.smoothInterior _ shiftedMembership).contDiffAt
    (openUnitCylinder_isOpen.mem_nhds shiftedMembership)
  have affineSmooth : ContDiffAt ℝ ∞
      (fun parameter : ℝ => point + parameter • spatialCellBasis 2) scale := by
    fun_prop
  exact outerSmooth.comp scale affineSmooth

theorem iteratedDeriv_diskCellLift_cellLine
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (point : SpatialCell) (membership : point ∈ openUnitCylinder)
    (order : ℕ) :
    iteratedDeriv order (fun scale : ℝ =>
      diskCellLift field.value (point + scale • spatialCellBasis 2)) 0 =
      closedMixedDerivative field order (pureCellWord order)
        (diskCellPoint point (openCylinderMembershipClosed point membership)) := by
  calc
    iteratedDeriv order (fun scale : ℝ =>
        diskCellLift field.value (point + scale • spatialCellBasis 2)) 0 =
        mixedCartesianDerivative order (pureCellWord order)
          (diskCellLift field.value) point := by
      symm
      apply pureCellMixedDerivative_eq_iteratedDeriv_line
      intro scale
      have shiftedMembership :
          point + scale • spatialCellBasis 2 ∈ openUnitCylinder := by
        change ‖planarPart (point + scale • spatialCellBasis 2)‖ < 1
        rw [planarPart_add_smul_cellBasis]
        exact membership
      exact (field.smoothInterior _ shiftedMembership).contDiffAt
        (openUnitCylinder_isOpen.mem_nhds shiftedMembership)
    _ = closedMixedDerivative field order (pureCellWord order)
        (diskCellPoint point
          (openCylinderMembershipClosed point membership)) :=
      (closedMixedDerivative_spec field order (pureCellWord order)
        point membership).symm

theorem assemble_reflectedPoint_cellLine (index : ℕ)
    (point : SpatialCell) (scale : ℝ) :
    assembleSpatialCell (reflectedPoint index (planarPart point))
        (point 2 + scale) =
      reflectedSpatialCell index point + scale • spatialCellBasis 2 := by
  rw [← reflectedSpatialCell_add_smul_cellBasis]
  unfold reflectedSpatialCell
  rw [planarPart_add_smul_cellBasis, cellCoordinate_add_smul_cellBasis]

theorem exteriorSummand_cellLine_eq_real_smul
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (index : ℕ) (point : SpatialCell) :
    (fun scale : ℝ =>
      exteriorSummandFromValue field.value index (planarPart point)
        ((point 2 + scale : ℝ) : CellCircle)) =
      (fun scale : ℝ =>
        (coefficient index *
          plateauCutoff (node index * (‖planarPart point‖ - 1))) •
        diskCellLift field.value
          (reflectedSpatialCell index point + scale • spatialCellBasis 2)) := by
  funext scale
  rw [exteriorSummandFromValue,
    closedDiskLift_eq_diskCellLift_assemble,
    assemble_reflectedPoint_cellLine]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ)
    (coefficient index *
      plateauCutoff (node index * (‖planarPart point‖ - 1))) _)

theorem exteriorSummand_cellLine_contDiff
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (index : ℕ) (point : SpatialCell)
    (outside : 1 < ‖planarPart point‖) :
    ContDiff ℝ ∞ (fun scale : ℝ =>
      exteriorSummandFromValue field.value index (planarPart point)
        ((point 2 + scale : ℝ) : CellCircle)) := by
  by_cases cutoffZero :
      plateauCutoff (node index * (‖planarPart point‖ - 1)) = 0
  · have functionZero : (fun scale : ℝ =>
        exteriorSummandFromValue field.value index (planarPart point)
          ((point 2 + scale : ℝ) : CellCircle)) = 0 := by
      funext scale
      simp [exteriorSummandFromValue, cutoffZero]
    rw [functionZero]
    exact contDiff_const
  · have reflectedOpen : reflectedPoint index (planarPart point) ∈ openUnitDisk :=
      cutoff_nonzero_reflectedPoint_mem_openUnitDisk
        index (planarPart point) outside cutoffZero
    have reflectedCylinder : reflectedSpatialCell index point ∈
        openUnitCylinder := by
      change ‖planarPart (reflectedSpatialCell index point)‖ < 1
      rw [reflectedSpatialCell_planarPart]
      exact reflectedOpen
    rw [exteriorSummand_cellLine_eq_real_smul field index point]
    exact (diskCellLift_cellLine_contDiff field
      (reflectedSpatialCell index point) reflectedCylinder).const_smul _

theorem iteratedDeriv_exteriorSummand_cellLine
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (index order : ℕ) (point : SpatialCell)
    (outside : 1 < ‖planarPart point‖) :
    iteratedDeriv order (fun scale : ℝ =>
      exteriorSummandFromValue field.value index (planarPart point)
        ((point 2 + scale : ℝ) : CellCircle)) 0 =
      exteriorSummandFromValue
        (closedMixedDerivative field order (pureCellWord order))
        index (planarPart point) (point 2 : CellCircle) := by
  by_cases cutoffZero :
      plateauCutoff (node index * (‖planarPart point‖ - 1)) = 0
  · have functionZero : (fun scale : ℝ =>
        exteriorSummandFromValue field.value index (planarPart point)
          ((point 2 + scale : ℝ) : CellCircle)) = 0 := by
      funext scale
      simp [exteriorSummandFromValue, cutoffZero]
    rw [functionZero]
    simp [exteriorSummandFromValue, cutoffZero]
  · have reflectedOpen : reflectedPoint index (planarPart point) ∈ openUnitDisk :=
      cutoff_nonzero_reflectedPoint_mem_openUnitDisk
        index (planarPart point) outside cutoffZero
    have reflectedCylinder : reflectedSpatialCell index point ∈
        openUnitCylinder := by
      change ‖planarPart (reflectedSpatialCell index point)‖ < 1
      rw [reflectedSpatialCell_planarPart]
      exact reflectedOpen
    let scalar : ℝ := coefficient index *
      plateauCutoff (node index * (‖planarPart point‖ - 1))
    have functionEquality :=
      exteriorSummand_cellLine_eq_real_smul field index point
    rw [functionEquality]
    change iteratedDeriv order (scalar • (fun scale : ℝ =>
      diskCellLift field.value
        (reflectedSpatialCell index point + scale • spatialCellBasis 2))) 0 = _
    rw [iteratedDeriv_const_smul (𝕜 := ℝ) (R := ℝ)
      ((diskCellLift_cellLine_contDiff field
        (reflectedSpatialCell index point) reflectedCylinder).of_le
          (WithTop.coe_le_coe.mpr
            (show (order : ℕ∞) ≤ ⊤ from le_top))).contDiffAt scalar]
    rw [iteratedDeriv_diskCellLift_cellLine
      field (reflectedSpatialCell index point) reflectedCylinder order]
    rw [exteriorSummandFromValue]
    rw [closedDiskLift, dif_pos
      (openDiskMembershipClosed _ reflectedOpen)]
    rw [show diskCellPoint (reflectedSpatialCell index point)
        (openCylinderMembershipClosed _ reflectedCylinder) =
        (⟨reflectedPoint index (planarPart point),
          openDiskMembershipClosed _ reflectedOpen⟩,
          (point 2 : CellCircle)) by
      apply Prod.ext
      · apply Subtype.ext
        exact reflectedSpatialCell_planarPart index point
      · rfl]
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) scalar _).symm

theorem iteratedDeriv_exteriorSeries_cellLine
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (order : ℕ) (point : SpatialCell)
    (outside : 1 < ‖planarPart point‖) :
    iteratedDeriv order (fun scale : ℝ =>
      exteriorSeriesFromValue field.value (planarPart point)
        ((point 2 + scale : ℝ) : CellCircle)) 0 =
      exteriorSeriesFromValue
        (closedMixedDerivative field order (pureCellWord order))
        (planarPart point) (point 2 : CellCircle) := by
  have tailEvent := eventually_cutoff_zero (planarPart point) outside
  rw [Filter.eventually_atTop] at tailEvent
  obtain ⟨cutoff, cutoffProperty⟩ := tailEvent
  have valueFinite : (fun scale : ℝ =>
      exteriorSeriesFromValue field.value (planarPart point)
        ((point 2 + scale : ℝ) : CellCircle)) =
      (fun scale : ℝ => ∑ index ∈ Finset.range cutoff,
        exteriorSummandFromValue field.value index (planarPart point)
          ((point 2 + scale : ℝ) : CellCircle)) := by
    funext scale
    unfold exteriorSeriesFromValue
    exact (hasSum_sum_of_ne_finset_zero fun index outsideRange => by
      simp [exteriorSummandFromValue,
        cutoffProperty index (by simpa using outsideRange)]).tsum_eq
  have derivativeFinite :
      exteriorSeriesFromValue
        (closedMixedDerivative field order (pureCellWord order))
        (planarPart point) (point 2 : CellCircle) =
      ∑ index ∈ Finset.range cutoff,
        exteriorSummandFromValue
          (closedMixedDerivative field order (pureCellWord order))
          index (planarPart point) (point 2 : CellCircle) := by
    unfold exteriorSeriesFromValue
    exact (hasSum_sum_of_ne_finset_zero fun index outsideRange => by
      simp [exteriorSummandFromValue,
        cutoffProperty index (by simpa using outsideRange)]).tsum_eq
  rw [valueFinite]
  rw [iteratedDeriv_fun_sum]
  · rw [derivativeFinite]
    apply Finset.sum_congr rfl
    intro index _
    exact iteratedDeriv_exteriorSummand_cellLine
      field index order point outside
  · intro index _
    exact (exteriorSummand_cellLine_contDiff field index point outside).of_le
      (WithTop.coe_le_coe.mpr
        (show (order : ℕ∞) ≤ ⊤ from le_top)) |>.contDiffAt

theorem ambientExtension_pureCellDerivative
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (order : ℕ) (point : SpatialCell) :
    mixedCartesianDerivative order (pureCellWord order)
        (ambientExtensionCellLift field) point =
      ambientExtensionFromValue
        (closedMixedDerivative field order (pureCellWord order))
        (planarPart point) (point 2 : CellCircle) := by
  by_cases inside : ‖planarPart point‖ ≤ 1
  · have cylinderInside : point ∈ closedUnitCylinder := inside
    have diskInside : planarPart point ∈ closedUnitDisk := inside
    rw [mixedCartesianDerivative,
      ← ambientHigherDerivative_eq_iteratedFDeriv_ambient field order point,
      ambientHigherDerivative, if_pos inside,
      closedHigherDerivative_basis,
      retractedDiskCell_eq_diskCellPoint point cylinderInside,
      ambientExtensionFromValue, dif_pos diskInside]
    congr 2
  · have outside : 1 < ‖planarPart point‖ := lt_of_not_ge inside
    have diskOutside : planarPart point ∉ closedUnitDisk := inside
    have cellLineEquality : (fun scale : ℝ =>
        ambientExtensionCellLift field
          (point + scale • spatialCellBasis 2)) =
        (fun scale : ℝ =>
          exteriorSeriesFromValue field.value (planarPart point)
            ((point 2 + scale : ℝ) : CellCircle)) := by
      funext scale
      rw [ambientExtensionCellLift, planarPart_add_smul_cellBasis,
        cellCoordinate_add_smul_cellBasis,
        ambientExtensionFromValue, dif_neg diskOutside]
    calc
      mixedCartesianDerivative order (pureCellWord order)
          (ambientExtensionCellLift field) point =
          iteratedDeriv order (fun scale : ℝ =>
            ambientExtensionCellLift field
              (point + scale • spatialCellBasis 2)) 0 := by
        apply pureCellMixedDerivative_eq_iteratedDeriv_line
        intro scale
        exact (ambientExtensionCellLift_contDiff_infty field).contDiffAt
      _ = iteratedDeriv order (fun scale : ℝ =>
            exteriorSeriesFromValue field.value (planarPart point)
              ((point 2 + scale : ℝ) : CellCircle)) 0 := by
        rw [cellLineEquality]
      _ = exteriorSeriesFromValue
            (closedMixedDerivative field order (pureCellWord order))
            (planarPart point) (point 2 : CellCircle) :=
        iteratedDeriv_exteriorSeries_cellLine field order point outside
      _ = ambientExtensionFromValue
            (closedMixedDerivative field order (pureCellWord order))
            (planarPart point) (point 2 : CellCircle) := by
        rw [ambientExtensionFromValue, dif_neg diskOutside]

theorem periodizedSpatialCellRepresentative_add_smul_cellBasis
    (point : SpatialCell) (scale : ℝ) :
    periodizedSpatialCellRepresentative
        (point + scale • spatialCellBasis 2) =
      periodizedSpatialCellRepresentative point +
        scale • spatialCellBasis 2 := by
  unfold periodizedSpatialCellRepresentative
  rw [planarPart_add_smul_cellBasis,
    cellCoordinate_add_smul_cellBasis]
  ext coordinate
  fin_cases coordinate
  · simp [assembleSpatialCell, spatialCellBasis]
  · simp [assembleSpatialCell, spatialCellBasis]
  · simp [assembleSpatialCell, spatialCellBasis]

theorem torusCellLift_periodizedExtensionValue_cellLine
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (point : SpatialCell) :
    (fun scale : ℝ =>
      torusCellLift (periodizedExtension field).value
        (point + scale • spatialCellBasis 2)) =
      (fun scale : ℝ =>
        ambientExtensionCellLift field
          (periodizedSpatialCellRepresentative point +
            scale • spatialCellBasis 2)) := by
  funext scale
  change torusCellLift (periodizedExtensionValue field)
      (point + scale • spatialCellBasis 2) = _
  rw [torusCellLift_periodizedExtensionValue,
    periodizedSpatialCellRepresentative_add_smul_cellBasis]

theorem periodizedExtension_pureCellDerivative_on_lift
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (order : ℕ) (point : SpatialCell) :
    mixedCartesianDerivative order (pureCellWord order)
        (torusCellLift (periodizedExtension field).value) point =
      periodizedExtensionFromValue
        (closedMixedDerivative field order (pureCellWord order))
        (torusCellPoint point) := by
  calc
    mixedCartesianDerivative order (pureCellWord order)
        (torusCellLift (periodizedExtension field).value) point =
        iteratedDeriv order (fun scale : ℝ =>
          torusCellLift (periodizedExtension field).value
            (point + scale • spatialCellBasis 2)) 0 := by
      apply pureCellMixedDerivative_eq_iteratedDeriv_line
      intro scale
      exact (periodizedExtension field).smoothLift.contDiffAt
    _ = iteratedDeriv order (fun scale : ℝ =>
          ambientExtensionCellLift field
            (periodizedSpatialCellRepresentative point +
              scale • spatialCellBasis 2)) 0 := by
      rw [torusCellLift_periodizedExtensionValue_cellLine]
    _ = mixedCartesianDerivative order (pureCellWord order)
          (ambientExtensionCellLift field)
          (periodizedSpatialCellRepresentative point) := by
      symm
      apply pureCellMixedDerivative_eq_iteratedDeriv_line
      intro scale
      exact (ambientExtensionCellLift_contDiff_infty field).contDiffAt
    _ = ambientExtensionFromValue
          (closedMixedDerivative field order (pureCellWord order))
          (planarPart (periodizedSpatialCellRepresentative point))
          ((periodizedSpatialCellRepresentative point) 2 : CellCircle) :=
      ambientExtension_pureCellDerivative field order
        (periodizedSpatialCellRepresentative point)
    _ = periodizedExtensionFromValue
          (closedMixedDerivative field order (pureCellWord order))
          (torusCellPoint point) := by
      rfl

theorem periodizedExtension_cell_commutes
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (order : ℕ) (point : TorusCellDomain) :
    torusDerivative (periodizedExtension field) order (pureCellWord order) point =
      periodizedExtensionFromValue
        (closedMixedDerivative field order (pureCellWord order)) point := by
  obtain ⟨representative, rfl⟩ := torusCellPoint_surjective point
  rw [torusDerivative_spec]
  exact periodizedExtension_pureCellDerivative_on_lift
    field order representative

theorem ordinaryExtensionRetraction_cell_commutation :
    CellDerivativeCommutationGoal ordinaryExtensionRetraction := by
  constructor
  · intro dimension field order point
    exact periodizedExtension_cell_commutes field order point
  · intro dimension field order point
    exact torusRestriction_cell_commutes field order point

end Grad.DiskExtension.Operator
