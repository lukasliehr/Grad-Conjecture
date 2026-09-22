import P0910PeriodizedSmooth
import P0910Algebra

noncomputable section

open Filter Set
open scoped BigOperators ContDiff Topology

namespace Grad.DiskExtension.Operator

open Grad.ClosedJets

noncomputable def ordinaryExtensionRetraction : OrdinaryExtensionRetraction where
  extension := fun _ => periodizedExtension
  restriction := fun _ => torusRestriction

theorem ordinaryExtensionRetraction_construction :
    ConstructionFormulaGoal ordinaryExtensionRetraction := by
  constructor
  · intro dimension field point
    rfl
  · intro dimension field point
    rfl

theorem spatialTorusRepresentative_torusCellPoint_assemble
    (point : SpatialPlane) (cell : ℝ)
    (membership : point ∈ fundamentalHalfOpenSquare) :
    spatialTorusRepresentative
      (torusCellPoint (assembleSpatialCell point cell)).1 = point := by
  rw [fundamentalHalfOpenSquare] at membership
  ext coordinate
  fin_cases coordinate
  · change (AddCircle.equivIco (4 : ℝ) (-2)
      (point 0 : SpatialCircle)).val = point 0
    exact congrArg Subtype.val (AddCircle.equivIco_coe_eq
      ⟨membership.1, by norm_num; exact membership.2.1⟩)
  · change (AddCircle.equivIco (4 : ℝ) (-2)
      (point 1 : SpatialCircle)).val = point 1
    exact congrArg Subtype.val (AddCircle.equivIco_coe_eq
      ⟨membership.2.2.1, by norm_num; exact membership.2.2.2⟩)

theorem periodizedExtension_fundamental_formula {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialPlane) (cell : ℝ)
    (membership : point ∈ fundamentalHalfOpenSquare) :
    torusCellLift (periodizedExtension field).value
        (assembleSpatialCell point cell) =
      ambientExtensionFromValue field.value point (cell : CellCircle) := by
  change periodizedExtensionFromValue field.value
      (torusCellPoint (assembleSpatialCell point cell)) = _
  rw [periodizedExtensionFromValue,
    spatialTorusRepresentative_torusCellPoint_assemble point cell membership]
  rfl

theorem ordinaryExtensionRetraction_smooth_boundary_support :
    SmoothBoundarySupportGoal ordinaryExtensionRetraction := by
  intro dimension field
  refine ⟨ambientExtensionCellLift_contDiff_infty field,
    (ambientExtensionCellLift_contDiff_infty field).contDiffOn, ?_, ?_, ?_, ?_, ?_⟩
  · intro point membership cell
    exact ambientExtension_inside field.value point membership cell
  · intro point boundary order word
    exact mixedCartesianDerivative_boundary_all_orders
      field point boundary order word
  · intro point cell outside
    exact ambientExtension_zero_of_support field.value point cell outside
  · intro cell
    exact ambientExtension_tsupport_subset field.value cell
  · intro point cell membership
    exact periodizedExtension_fundamental_formula field point cell membership

theorem ordinaryExtensionRetraction_retracts {dimension : ℕ}
    (field : DiskCellClosedJet dimension) :
    torusRestriction (periodizedExtension field) = field := by
  apply diskCellClosedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  exact periodizedExtension_restricts field point

theorem ordinaryExtensionRetraction_extension_add {dimension : ℕ}
    (first second : DiskCellClosedJet dimension) (point : TorusCellDomain) :
    (periodizedExtension (diskCellClosedJetAdd first second)).value point =
      (periodizedExtension first).value point +
        (periodizedExtension second).value point :=
  periodizedExtension_add first second point

theorem ordinaryExtensionRetraction_extension_smul {dimension : ℕ}
    (scalar : ℂ) (field : DiskCellClosedJet dimension)
    (point : TorusCellDomain) :
    (periodizedExtension (diskCellClosedJetSmul scalar field)).value point =
      scalar • (periodizedExtension field).value point :=
  periodizedExtension_smul scalar field point

theorem ordinaryExtensionRetraction_linearity_restriction :
    ( ∀ dimension (first second : DiskCellClosedJet dimension) point,
        (ordinaryExtensionRetraction.extension dimension
          (diskCellClosedJetAdd first second)).value point =
        (ordinaryExtensionRetraction.extension dimension first).value point +
          (ordinaryExtensionRetraction.extension dimension second).value point) ∧
    ( ∀ dimension (scalar : ℂ) (field : DiskCellClosedJet dimension) point,
        (ordinaryExtensionRetraction.extension dimension
          (diskCellClosedJetSmul scalar field)).value point =
        scalar • (ordinaryExtensionRetraction.extension dimension field).value point) ∧
    ( ∀ dimension (sum first second : TorusSmoothField dimension),
        IsTorusValuewiseAdd sum first second →
          IsDiskCellValuewiseAdd
            (ordinaryExtensionRetraction.restriction dimension sum)
            (ordinaryExtensionRetraction.restriction dimension first)
            (ordinaryExtensionRetraction.restriction dimension second)) ∧
    ( ∀ dimension (scalar : ℂ) (scaled field : TorusSmoothField dimension),
        IsTorusValuewiseSmul scalar scaled field →
          IsDiskCellValuewiseSmul scalar
            (ordinaryExtensionRetraction.restriction dimension scaled)
            (ordinaryExtensionRetraction.restriction dimension field)) ∧
    ( ∀ dimension (field : TorusSmoothField dimension),
        IsRealTorusField field →
          IsRealDiskCellField
            (ordinaryExtensionRetraction.restriction dimension field)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro dimension first second point
    exact ordinaryExtensionRetraction_extension_add first second point
  · intro dimension scalar field point
    exact ordinaryExtensionRetraction_extension_smul scalar field point
  · intro dimension sum first second addition
    exact torusRestriction_add sum first second addition
  · intro dimension scalar scaled field scaling
    exact torusRestriction_smul scalar scaled field scaling
  · intro dimension field real
    exact torusRestriction_real field real

theorem closedDiskLift_real {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (real : IsRealDiskCellField field)
    (point : SpatialPlane) (cell : CellCircle) :
    IsRealVector (closedDiskLift
      (fun diskPoint => field.value (diskPoint, cell)) point) := by
  intro coordinate
  classical
  by_cases membership : point ∈ closedUnitDisk
  · rw [closedDiskLift, dif_pos membership]
    exact real (⟨point, membership⟩, cell) coordinate
  · simp [closedDiskLift, membership]

theorem exteriorSummand_real {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (real : IsRealDiskCellField field)
    (index : ℕ) (point : SpatialPlane) (cell : CellCircle) :
    IsRealVector (exteriorSummandFromValue field.value index point cell) := by
  intro coordinate
  rw [exteriorSummandFromValue]
  simp only [PiLp.smul_apply, star_smul]
  have scalarReal :
      star (((Seeley.coefficient index *
        plateauCutoff (Seeley.node index * (‖point‖ - 1)) : ℝ) : ℂ)) =
      (((Seeley.coefficient index *
        plateauCutoff (Seeley.node index * (‖point‖ - 1)) : ℝ) : ℂ)) := by
    simp
  rw [scalarReal]
  rw [closedDiskLift_real field real (reflectedPoint index point) cell coordinate]

theorem exteriorSeries_real {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (real : IsRealDiskCellField field)
    (point : SpatialPlane) (cell : CellCircle) :
    IsRealVector (exteriorSeriesFromValue field.value point cell) := by
  intro coordinate
  unfold exteriorSeriesFromValue
  have coordinateTsum :
      (∑' index, exteriorSummandFromValue field.value index point cell) coordinate =
      ∑' index, exteriorSummandFromValue field.value index point cell coordinate := by
    simpa using (PiLp.proj (p := (2 : ENNReal)) (𝕜 := ℂ)
      (fun _ : Fin dimension => ℂ) coordinate).map_tsum
        (exteriorSummand_summable field.value point cell)
  rw [coordinateTsum]
  rw [show star (∑' index,
      exteriorSummandFromValue field.value index point cell coordinate) =
      ∑' index, star
        (exteriorSummandFromValue field.value index point cell coordinate) by
    simpa only [RCLike.conjCLE_apply, RCLike.star_def] using
      (RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).map_tsum
        (f := fun index =>
          exteriorSummandFromValue field.value index point cell coordinate)]
  congr 1
  funext index
  exact exteriorSummand_real field real index point cell coordinate

theorem ambientExtension_real {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (real : IsRealDiskCellField field)
    (point : SpatialPlane) (cell : CellCircle) :
    IsRealVector (ambientExtensionFromValue field.value point cell) := by
  classical
  by_cases membership : point ∈ closedUnitDisk
  · rw [ambientExtensionFromValue, dif_pos membership]
    exact real (⟨point, membership⟩, cell)
  · rw [ambientExtensionFromValue, dif_neg membership]
    exact exteriorSeries_real field real point cell

theorem periodizedExtension_real {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (real : IsRealDiskCellField field) :
    IsRealTorusField (periodizedExtension field) := by
  intro point
  exact ambientExtension_real field real
    (spatialTorusRepresentative point.1) point.2

theorem ordinaryExtensionRetraction_linearity_real :
    RetractionLinearityRealGoal ordinaryExtensionRetraction := by
  refine ⟨?_,
    ordinaryExtensionRetraction_linearity_restriction.1,
    ordinaryExtensionRetraction_linearity_restriction.2.1,
    ordinaryExtensionRetraction_linearity_restriction.2.2.1,
    ordinaryExtensionRetraction_linearity_restriction.2.2.2.1,
    ?_, ordinaryExtensionRetraction_linearity_restriction.2.2.2.2⟩
  · intro dimension field
    exact ordinaryExtensionRetraction_retracts field
  · intro dimension field real
    exact periodizedExtension_real field real

end Grad.DiskExtension.Operator
