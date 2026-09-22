import P0910Series

noncomputable section

open Set
open scoped ContDiff Topology

namespace Grad.DiskExtension.Operator

open Grad.ClosedJets

theorem torusSmoothField_eq_of_value_eq {dimension : ℕ}
    (first second : TorusSmoothField dimension) (equality : first.value = second.value) :
    first = second := by
  cases first
  cases second
  cases equality
  rfl

theorem torusDerivative_spec {dimension : ℕ} (field : TorusSmoothField dimension)
    (order : ℕ) (word : MixedCartesianWord order) (point : SpatialCell) :
    torusDerivative field order word (torusCellPoint point) =
      mixedCartesianDerivative order word (torusCellLift field.value) point :=
  Classical.choose_spec (field.derivativeExists order word) point

theorem torusCellPoint_surjective : Function.Surjective torusCellPoint := by
  rintro ⟨⟨first, second⟩, cell⟩
  obtain ⟨firstRep, rfl⟩ := QuotientAddGroup.mk_surjective first
  obtain ⟨secondRep, rfl⟩ := QuotientAddGroup.mk_surjective second
  obtain ⟨cellRep, rfl⟩ := QuotientAddGroup.mk_surjective cell
  refine ⟨assembleSpatialCell
    (WithLp.toLp 2 ![firstRep, secondRep]) cellRep, ?_⟩
  rfl

theorem torusDerivative_unique {dimension : ℕ} (field : TorusSmoothField dimension)
    (order : ℕ) (word : MixedCartesianWord order)
    (extension : ContinuousMap TorusCellDomain (ComplexEuclidean dimension))
    (extension_spec : ∀ point : SpatialCell,
      extension (torusCellPoint point) =
        mixedCartesianDerivative order word (torusCellLift field.value) point) :
    extension = torusDerivative field order word := by
  apply ContinuousMap.ext
  intro point
  obtain ⟨representative, rfl⟩ := torusCellPoint_surjective point
  rw [extension_spec, torusDerivative_spec]

theorem continuous_diskToTorus : Continuous diskToTorus := by
  unfold diskToTorus
  fun_prop

def torusRestrictionValue {dimension : ℕ} (field : TorusSmoothField dimension) :
    ContinuousMap DiskCellDomain (ComplexEuclidean dimension) where
  toFun := fun point => field.value (diskToTorus point)
  continuous_toFun := field.value.continuous.comp continuous_diskToTorus

def torusDerivativeRestrictionValue {dimension : ℕ} (field : TorusSmoothField dimension)
    (order : ℕ) (word : MixedCartesianWord order) :
    ContinuousMap DiskCellDomain (ComplexEuclidean dimension) where
  toFun := fun point => torusDerivative field order word (diskToTorus point)
  continuous_toFun := (torusDerivative field order word).continuous.comp continuous_diskToTorus

@[simp] theorem diskToTorus_diskCellPoint (point : SpatialCell)
    (membership : point ∈ closedUnitCylinder) :
    diskToTorus (diskCellPoint point membership) = torusCellPoint point := by
  rfl

theorem restriction_lift_eq_on_open {dimension : ℕ} (field : TorusSmoothField dimension) :
    Set.EqOn (diskCellLift (torusRestrictionValue field))
      (torusCellLift field.value) openUnitCylinder := by
  intro point membership
  rw [diskCellLift, dif_pos (openCylinderMembershipClosed point membership)]
  rfl

theorem restriction_mixedDerivative_eq {dimension : ℕ}
    (field : TorusSmoothField dimension) (order : ℕ)
    (word : MixedCartesianWord order) (point : SpatialCell)
    (membership : point ∈ openUnitCylinder) :
    mixedCartesianDerivative order word (diskCellLift (torusRestrictionValue field)) point =
      mixedCartesianDerivative order word (torusCellLift field.value) point := by
  have withinEquality := iteratedFDerivWithin_congr (𝕜 := ℝ)
    (restriction_lift_eq_on_open field) membership order
  rw [iteratedFDerivWithin_of_isOpen order openUnitCylinder_isOpen membership,
    iteratedFDerivWithin_of_isOpen order openUnitCylinder_isOpen membership] at withinEquality
  exact congrArg (fun derivative =>
    derivative (fun position => spatialCellBasis (word position))) withinEquality

theorem torusDerivativeRestrictionValue_spec {dimension : ℕ}
    (field : TorusSmoothField dimension) (order : ℕ)
    (word : MixedCartesianWord order) :
    IsMixedCartesianExtension (torusRestrictionValue field) order word
      (torusDerivativeRestrictionValue field order word) := by
  intro point membership
  rw [show torusDerivativeRestrictionValue field order word
      (diskCellPoint point (openCylinderMembershipClosed point membership)) =
      torusDerivative field order word (torusCellPoint point) from rfl]
  rw [torusDerivative_spec]
  exact (restriction_mixedDerivative_eq field order word point membership).symm

def torusRestriction {dimension : ℕ} (field : TorusSmoothField dimension) :
    DiskCellClosedJet dimension where
  value := torusRestrictionValue field
  smoothInterior :=
    field.smoothLift.contDiffOn.congr
      (fun _ membership => restriction_lift_eq_on_open field membership)
  derivativeExists := fun order word =>
    ⟨torusDerivativeRestrictionValue field order word,
      torusDerivativeRestrictionValue_spec field order word⟩

theorem torusRestriction_value {dimension : ℕ} (field : TorusSmoothField dimension)
    (point : DiskCellDomain) :
    (torusRestriction field).value point = field.value (diskToTorus point) := rfl

theorem torusRestriction_derivative {dimension : ℕ} (field : TorusSmoothField dimension)
    (order : ℕ) (word : MixedCartesianWord order) :
    closedMixedDerivative (torusRestriction field) order word =
      torusDerivativeRestrictionValue field order word := by
  symm
  apply mixedCartesianExtension_unique
  exact torusDerivativeRestrictionValue_spec field order word

theorem torusRestriction_cell_commutes {dimension : ℕ}
    (field : TorusSmoothField dimension) (order : ℕ) (point : DiskCellDomain) :
    closedMixedDerivative (torusRestriction field) order (pureCellWord order) point =
      torusDerivative field order (pureCellWord order) (diskToTorus point) := by
  rw [torusRestriction_derivative]
  rfl

theorem torusRestriction_add {dimension : ℕ}
    (sum first second : TorusSmoothField dimension)
    (addition : IsTorusValuewiseAdd sum first second) :
    IsDiskCellValuewiseAdd (torusRestriction sum)
      (torusRestriction first) (torusRestriction second) := by
  intro point
  exact addition (diskToTorus point)

theorem torusRestriction_smul {dimension : ℕ} (scalar : ℂ)
    (scaled field : TorusSmoothField dimension)
    (scaling : IsTorusValuewiseSmul scalar scaled field) :
    IsDiskCellValuewiseSmul scalar (torusRestriction scaled) (torusRestriction field) := by
  intro point
  exact scaling (diskToTorus point)

theorem torusRestriction_real {dimension : ℕ} (field : TorusSmoothField dimension)
    (real : IsRealTorusField field) : IsRealDiskCellField (torusRestriction field) := by
  intro point
  exact real (diskToTorus point)

end Grad.DiskExtension.Operator
