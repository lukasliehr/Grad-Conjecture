import GQC6CoherentDifferentials

noncomputable section

set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Radial

def ClosedTowerCompatible {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (family : CartesianMultiIndex → C(ClosedDisk, Value)) : Prop :=
  ∀ (index : CartesianMultiIndex) (point : SpatialPlane), point ∈ openUnitDisk →
    HasFDerivAt (closedDiskLift (family index))
      (planarDerivative (closedDiskLift (family (1 + index.1, index.2)) point)
        (closedDiskLift (family (index.1, 1 + index.2)) point)) point

theorem closedTower_contDiffOn_nat {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (family : CartesianMultiIndex → C(ClosedDisk, Value)) (compatible : ClosedTowerCompatible family)
    (order : ℕ) (index : CartesianMultiIndex) :
    ContDiffOn ℝ order (closedDiskLift (family index)) openUnitDisk := by
  induction order generalizing index with
  | zero =>
    change ContDiffOn ℝ (0 : WithTop ℕ∞) (closedDiskLift (family index)) openUnitDisk
    rw [contDiffOn_zero]
    intro point inside
    exact (compatible index point inside).continuousAt.continuousWithinAt
  | succ order induction =>
    rw [show (order.succ : WithTop ℕ∞) = (order : WithTop ℕ∞) + 1 by norm_num]
    apply (contDiffOn_succ_iff_fderiv_of_isOpen openUnitDisk_isOpen).mpr
    refine ⟨fun point inside => (compatible index point inside).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · intro impossible
      norm_num at impossible
    · have first := ((ContinuousLinearMap.smulRightL ℝ SpatialPlane Value)
        (planarCoordinate 0)).contDiff.fun_comp_contDiffOn (induction (1 + index.1, index.2))
      have second := ((ContinuousLinearMap.smulRightL ℝ SpatialPlane Value)
        (planarCoordinate 1)).contDiff.fun_comp_contDiffOn (induction (index.1, 1 + index.2))
      exact (first.add second).congr (fun point inside => (compatible index point inside).fderiv)

theorem closedTower_contDiffOn {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (family : CartesianMultiIndex → C(ClosedDisk, Value)) (compatible : ClosedTowerCompatible family)
    (index : CartesianMultiIndex) : ContDiffOn ℝ ∞ (closedDiskLift (family index)) openUnitDisk :=
  contDiffOn_infty.mpr (fun order => closedTower_contDiffOn_nat family compatible order index)

theorem closedTower_listDerivative {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (family : CartesianMultiIndex → C(ClosedDisk, Value)) (compatible : ClosedTowerCompatible family)
    (word : List (Fin 2)) (index : CartesianMultiIndex) :
    Set.EqOn (operatorCartesianListDerivative word (closedDiskLift (family index)))
      (closedDiskLift (family (index.1 + word.count 0, index.2 + word.count 1))) openUnitDisk := by
  induction word generalizing index with
  | nil => intro point _; rfl
  | cons coordinate rest induction =>
    intro point inside
    have localEquality : operatorCartesianListDerivative rest (closedDiskLift (family index)) =ᶠ[𝓝 point]
        closedDiskLift (family (index.1 + rest.count 0, index.2 + rest.count 1)) :=
      Filter.eventually_of_mem (openUnitDisk_isOpen.mem_nhds inside) (induction index)
    change fderiv ℝ (operatorCartesianListDerivative rest (closedDiskLift (family index))) point
      (spatialBasis coordinate) = _
    rw [localEquality.fderiv_eq, (compatible _ point inside).fderiv, planarDerivative_basis]
    fin_cases coordinate <;>
      simp [Nat.add_comm, Nat.add_left_comm]

/-- The reconstructed derivatives agree with the actual iterated
Cartesian derivative, not merely with a formal successor array. -/
theorem closedTower_multiDerivative {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (family : CartesianMultiIndex → C(ClosedDisk, Value)) (compatible : ClosedTowerCompatible family)
    (index : CartesianMultiIndex) (point : ClosedDisk) (inside : point.val ∈ openUnitDisk) :
    cartesianMultiDerivative index (closedDiskLift (family (0, 0))) point.val = family index point := by
  have smooth := closedTower_contDiffOn family compatible (0, 0)
  have ordered := operatorCartesianListDerivative_ofFn openUnitDisk_isOpen
    (cartesianOrder index) (cartesianMultiIndexWord index) smooth inside
  have actual := closedTower_listDerivative family compatible (List.ofFn (cartesianMultiIndexWord index)) (0, 0) inside
  rw [ordered] at actual
  have counts : ((0 : ℕ) + (List.ofFn (cartesianMultiIndexWord index)).count 0,
      (0 : ℕ) + (List.ofFn (cartesianMultiIndexWord index)).count 1) = index := by
    rcases index with ⟨first, second⟩
    simp [list_ofFn_cartesianMultiIndexWord, List.count_append, List.count_replicate]
  rw [counts, closedLift_value _ point.val inside] at actual
  exact actual

end Grad.GaugeCoefficients.Physical.Compensated
