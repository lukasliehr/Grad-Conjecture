import AKBV6DiagonalGraphOriginalCore
import P0910Proof

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Grad.CartesianCoreRecovery
open Grad.ClosedJets Grad.CartesianState Grad.DiskExtension.Operator

def closedCylinderQuotient : C(ClosedDisk × ℝ, DiskCellDomain) :=
  ⟨fun point => (point.1,(point.2 : CellCircle)), continuous_fst.prodMk
    (QuotientAddGroup.continuous_mk.comp continuous_snd)⟩

theorem closedCylinderQuotient_isQuotientMap : Topology.IsQuotientMap closedCylinderQuotient :=
  (IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk).isQuotientMap

def closedCylinderDerivativeLift {dimension : ℕ} (value : C(DiskCellDomain, ComplexEuclidean dimension))
    (smooth : ContDiffOn ℝ ∞ (diskCellLift value) closedUnitCylinder)
    (order : ℕ) (word : MixedCartesianWord order) : C(ClosedDisk × ℝ, ComplexEuclidean dimension) where
  toFun point := iteratedFDerivWithin ℝ order (diskCellLift value) closedUnitCylinder
    (assembleSpatialCell point.1.val point.2) (fun index => spatialCellBasis (word index))
  continuous_toFun := by
    have assembled : Continuous (fun point : ClosedDisk × ℝ => assembleSpatialCell point.1.val point.2) :=
      assembleSpatialCellCLM.continuous.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin order => SpatialCell)
      (ComplexEuclidean dimension) (fun index => spatialCellBasis (word index))).continuous.comp
      ((smooth.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top)
        closedUnitCylinder_uniqueDiffOn).comp_continuous assembled
        (fun point => by
          change ‖planarPart (assembleSpatialCell point.1.val point.2)‖ ≤ 1
          rw [planarPart_assembleSpatialCell]
          exact point.1.property))

theorem closedCylinderDerivativeLift_interior {dimension : ℕ}
    (value : C(DiskCellDomain, ComplexEuclidean dimension))
    (smooth : ContDiffOn ℝ ∞ (diskCellLift value) closedUnitCylinder)
    (order : ℕ) (word : MixedCartesianWord order) (point : ClosedDisk) (inside : point.val ∈ openUnitDisk) (axial : ℝ) :
    closedCylinderDerivativeLift value smooth order word (point,axial) =
      mixedCartesianDerivative order word (diskCellLift value) (assembleSpatialCell point.val axial) := by
  have membership : assembleSpatialCell point.val axial ∈ openUnitCylinder := by
    change ‖planarPart (assembleSpatialCell point.val axial)‖ < 1
    rw [planarPart_assembleSpatialCell]
    exact inside
  have smoothAt := (smooth.mono openCylinderMembershipClosed).contDiffAt (openUnitCylinder_isOpen.mem_nhds membership)
  change iteratedFDerivWithin ℝ order (diskCellLift value) closedUnitCylinder _ _ = _
  rw [iteratedFDerivWithin_eq_iteratedFDeriv closedUnitCylinder_uniqueDiffOn
    (smoothAt.of_le (by exact_mod_cast le_top)) (openCylinderMembershipClosed _ membership)]
  rfl

theorem diskCellLift_axial_shift {dimension : ℕ} (value : C(DiskCellDomain, ComplexEuclidean dimension))
    (shift : ℝ) (zero : (shift : CellCircle) = 0) (point : SpatialCell) :
    diskCellLift value (point + assembleSpatialCell 0 shift) = diskCellLift value point := by
  have planar : planarPart (point + assembleSpatialCell 0 shift) = planarPart point := by
    ext coordinate
    fin_cases coordinate <;> simp [planarPart,assembleSpatialCell]
  have membership : point + assembleSpatialCell 0 shift ∈ closedUnitCylinder ↔ point ∈ closedUnitCylinder := by
    change ‖planarPart (point + assembleSpatialCell 0 shift)‖ ≤ 1 ↔ ‖planarPart point‖ ≤ 1
    rw [planar]
  unfold diskCellLift
  by_cases inside : point ∈ closedUnitCylinder
  · rw [dif_pos inside,dif_pos (membership.mpr inside)]
    apply congrArg value
    apply Prod.ext
    · exact Subtype.ext planar
    · change ((point 2 + shift : ℝ) : CellCircle) = (point 2 : CellCircle)
      rw [AddCircle.coe_add,zero,add_zero]
  · rw [dif_neg inside,dif_neg (fun h => inside (membership.mp h))]

theorem closedCylinderDerivativeLift_factors {dimension : ℕ}
    (value : C(DiskCellDomain, ComplexEuclidean dimension))
    (smooth : ContDiffOn ℝ ∞ (diskCellLift value) closedUnitCylinder)
    (order : ℕ) (word : MixedCartesianWord order) :
    Function.FactorsThrough (closedCylinderDerivativeLift value smooth order word) closedCylinderQuotient := by
  rintro ⟨first,one⟩ ⟨second,two⟩ same
  have planar : first = second := congrArg Prod.fst same
  subst second
  have cell : (one : CellCircle) = (two : CellCircle) := congrArg Prod.snd same
  have zero : ((two-one : ℝ) : CellCircle) = 0 := by rw [AddCircle.coe_sub,cell,sub_self]
  let firstMap : C(ClosedDisk,ComplexEuclidean dimension) :=
    (closedCylinderDerivativeLift value smooth order word).comp ⟨fun point => (point,one),continuous_id.prodMk continuous_const⟩
  let secondMap : C(ClosedDisk,ComplexEuclidean dimension) :=
    (closedCylinderDerivativeLift value smooth order word).comp ⟨fun point => (point,two),continuous_id.prodMk continuous_const⟩
  have equality : firstMap = secondMap := by
    apply continuousMap_eq_of_openDisk
    intro point inside
    change closedCylinderDerivativeLift value smooth order word (point,one) =
      closedCylinderDerivativeLift value smooth order word (point,two)
    rw [closedCylinderDerivativeLift_interior value smooth order word point inside,
      closedCylinderDerivativeLift_interior value smooth order word point inside]
    have shifted : (fun source => diskCellLift value (source + assembleSpatialCell 0 (two-one))) = diskCellLift value :=
      funext (diskCellLift_axial_shift value (two-one) zero)
    have pointEquality : assembleSpatialCell point.val one + assembleSpatialCell 0 (two-one) =
        assembleSpatialCell point.val two := by
      ext coordinate
      fin_cases coordinate <;> simp [assembleSpatialCell]
    unfold mixedCartesianDerivative
    conv_lhs => rw [← shifted]
    rw [iteratedFDeriv_comp_add_right,pointEquality]
  exact DFunLike.congr_fun equality first

def closedCylinderDerivative {dimension : ℕ} (value : C(DiskCellDomain, ComplexEuclidean dimension))
    (smooth : ContDiffOn ℝ ∞ (diskCellLift value) closedUnitCylinder)
    (order : ℕ) (word : MixedCartesianWord order) : C(DiskCellDomain, ComplexEuclidean dimension) :=
  closedCylinderQuotient_isQuotientMap.lift (closedCylinderDerivativeLift value smooth order word)
    (closedCylinderDerivativeLift_factors value smooth order word)

theorem closedCylinderDerivative_spec {dimension : ℕ} (value : C(DiskCellDomain, ComplexEuclidean dimension))
    (smooth : ContDiffOn ℝ ∞ (diskCellLift value) closedUnitCylinder)
    (order : ℕ) (word : MixedCartesianWord order) :
    IsMixedCartesianExtension value order word (closedCylinderDerivative value smooth order word) := by
  intro point inside
  let disk : ClosedDisk := ⟨planarPart point,openCylinderMembershipClosed point inside⟩
  have assembled : assembleSpatialCell (planarPart point) (point 2) = point := by
    ext coordinate
    fin_cases coordinate <;> rfl
  change closedCylinderDerivative value smooth order word (closedCylinderQuotient (disk,point 2)) = _
  change (closedCylinderDerivative value smooth order word).comp closedCylinderQuotient (disk,point 2) = _
  rw [closedCylinderDerivative,Topology.IsQuotientMap.lift_comp]
  rw [closedCylinderDerivativeLift_interior value smooth order word disk inside,assembled]

/-- Genuine smoothness within the original closed cylinder supplies every literal boundary jet; no extension or boundary-jet premise is needed. -/
def closedCylinderJet {dimension : ℕ} (value : C(DiskCellDomain, ComplexEuclidean dimension))
    (smooth : ContDiffOn ℝ ∞ (diskCellLift value) closedUnitCylinder) : DiskCellClosedJet dimension where
  value := value
  smoothInterior := smooth.mono openCylinderMembershipClosed
  derivativeExists order word := ⟨closedCylinderDerivative value smooth order word,
    closedCylinderDerivative_spec value smooth order word⟩

end Grad.CartesianCoreRecovery
