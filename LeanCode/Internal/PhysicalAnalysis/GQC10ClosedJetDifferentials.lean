import GQC9APClosedDerivatives

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra

theorem closedJet_first {dimension : ℕ} (field : ClosedJet dimension)
    (point : SpatialPlane) (inside : point ∈ openUnitDisk) :
    HasFDerivAt (closedDiskLift field.value)
      (planarDerivative (closedDiskLift (closedDerivative field 1 (fun _ => 0)) point)
        (closedDiskLift (closedDerivative field 1 (fun _ => 1)) point)) point := by
  have basis (coordinate : Fin 2) : fderiv ℝ (closedDiskLift field.value) point (spatialBasis coordinate) =
      closedDiskLift (closedDerivative field 1 (fun _ => coordinate)) point := by
    have specification := closedDerivative_spec field 1 (fun _ => coordinate)
      ⟨point, openDiskMembershipClosed point inside⟩ inside
    calc
      _ = cartesianDerivative 1 (fun _ => coordinate) (closedDiskLift field.value) point :=
        (iteratedFDeriv_one_apply (fun _ : Fin 1 => spatialBasis coordinate)).symm
      _ = closedDerivative field 1 (fun _ => coordinate)
          ⟨point, openDiskMembershipClosed point inside⟩ := specification.symm
      _ = _ := (closedLift_value _ point inside).symm
  have actual := (field.smoothInterior.differentiableOn (by simp) point inside).differentiableAt
    (openUnitDisk_isOpen.mem_nhds inside) |>.hasFDerivAt
  rw [linear_eq_planarDerivative (fderiv ℝ (closedDiskLift field.value) point), basis 0, basis 1] at actual
  exact actual

theorem shiftedCartesianIndex_canonical (fixed index : CartesianMultiIndex) :
    shiftedCartesianIndex (cartesianMultiIndexWord fixed) index =
      (index.1 + fixed.1, index.2 + fixed.2) := by
  simp [shiftedCartesianIndex, cartesianWordIndex, List.ofFn_fin_append,
    Grad.CartesianState.list_ofFn_cartesianMultiIndexWord, List.count_append, List.count_replicate]

theorem closedDerivative_first_zero {dimension : ℕ} (field : ClosedJet dimension) :
    closedDerivative field 1 (fun _ => 0) = closedMultiDerivative field (1, 0) := by
  rw [closedDerivative_eq_closedMultiDerivative_wordIndex]
  simp [cartesianWordIndex, List.ofFn_succ]

theorem closedDerivative_first_one {dimension : ℕ} (field : ClosedJet dimension) :
    closedDerivative field 1 (fun _ => 1) = closedMultiDerivative field (0, 1) := by
  rw [closedDerivative_eq_closedMultiDerivative_wordIndex]
  simp [cartesianWordIndex, List.ofFn_succ]

theorem closedJet_multi_hasFDerivAt {dimension : ℕ} (field : ClosedJet dimension)
    (index : CartesianMultiIndex) (point : SpatialPlane) (inside : point ∈ openUnitDisk) :
    HasFDerivAt (closedDiskLift (closedMultiDerivative field index))
      (planarDerivative
        (closedDiskLift (closedMultiDerivative field (1 + index.1, index.2)) point)
        (closedDiskLift (closedMultiDerivative field (index.1, 1 + index.2)) point)) point := by
  have actual := closedJet_first (shiftedClosedJet field (cartesianMultiIndexWord index)) point inside
  rw [shiftedClosedJet_value, closedDerivative_first_zero, closedDerivative_first_one,
    shiftedClosedJet_closedMultiDerivative, shiftedClosedJet_closedMultiDerivative,
    shiftedCartesianIndex_canonical, shiftedCartesianIndex_canonical] at actual
  change HasFDerivAt (closedDiskLift (closedMultiDerivative field index))
    (planarDerivative
      (closedDiskLift (closedMultiDerivative field (1 + index.1, 0 + index.2)) point)
      (closedDiskLift (closedMultiDerivative field (0 + index.1, 1 + index.2)) point)) point at actual
  rw [Nat.zero_add, Nat.zero_add] at actual
  exact actual

end Grad.GaugeCoefficients.Physical.Compensated
