import GQC10ClosedJetDifferentials

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger

abbrev apWeightedMultiDerivative {dimension grade : ℕ} (L sigma gamma ell : ℝ)
    (index : CartesianMultiIndex) (large : cartesianOrder index + 2 ≤ grade) (cell : ℤ) :
    apGrade L sigma gamma ell dimension grade →L[ℂ] C(ClosedDisk, ComplexEuclidean dimension) :=
  apWeightedDerivative L sigma gamma ell large cell (cartesianMultiIndexWord index)

theorem apWeightedMultiDerivative_core {dimension grade : ℕ} (L sigma gamma ell : ℝ)
    (index : CartesianMultiIndex) (large : cartesianOrder index + 2 ≤ grade) (cell : ℤ)
    (core : ℤ →₀ ClosedJet dimension) :
    apWeightedMultiDerivative L sigma gamma ell index large cell (apFiniteInto L sigma gamma ell core) =
      closedMultiDerivative (apWeightedJet sigma gamma ell cell (core cell)) index :=
  apWeightedDerivative_core L sigma gamma ell large cell (cartesianMultiIndexWord index) core

theorem apWeightedMultiDerivative_lowering {dimension low high : ℕ} (L sigma gamma ell : ℝ)
    (index : CartesianMultiIndex) (large : cartesianOrder index + 2 ≤ low) (ordered : low ≤ high) (cell : ℤ)
    (field : apGrade L sigma gamma ell dimension high) :
    apWeightedMultiDerivative L sigma gamma ell index large cell (apLowering L sigma gamma ell ordered field) =
      apWeightedMultiDerivative L sigma gamma ell index (large.trans ordered) cell field := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := dimension) (grade := high) L sigma gamma ell)
    (isClosed_eq ((apWeightedMultiDerivative L sigma gamma ell index large cell).continuous.comp
      (apLowering L sigma gamma ell ordered).continuous)
      (apWeightedMultiDerivative L sigma gamma ell index (large.trans ordered) cell).continuous) _ field
  intro core
  simp only [Function.comp_apply]
  rw [apLowering_core, apWeightedMultiDerivative_core, apWeightedMultiDerivative_core]

/-- Actual C¹ compatibility of every high-enough AP2 weighted derivative.
The proof is on the accepted finite closed-jet core and its exact completion. -/
theorem apWeightedMultiDerivative_hasFDerivAt {dimension grade : ℕ} (L sigma gamma ell : ℝ)
    (index : CartesianMultiIndex) (large : cartesianOrder index + 3 ≤ grade) (cell : ℤ)
    (field : apGrade L sigma gamma ell dimension grade) (point : SpatialPlane) (inside : point ∈ openUnitDisk) :
    HasFDerivAt
      (closedDiskLift (apWeightedMultiDerivative L sigma gamma ell index (by omega) cell field))
      (planarDerivative
        (closedDiskLift (apWeightedMultiDerivative L sigma gamma ell (1 + index.1, index.2)
          (by unfold cartesianOrder at *; omega) cell field) point)
        (closedDiskLift (apWeightedMultiDerivative L sigma gamma ell (index.1, 1 + index.2)
          (by unfold cartesianOrder at *; omega) cell field) point)) point := by
  let valueMap := apWeightedMultiDerivative (dimension := dimension) L sigma gamma ell index (by omega : cartesianOrder index + 2 ≤ grade) cell
  let firstMap := apWeightedMultiDerivative (dimension := dimension) L sigma gamma ell (1 + index.1, index.2)
    (by unfold cartesianOrder at *; omega : cartesianOrder (1 + index.1, index.2) + 2 ≤ grade) cell
  let secondMap := apWeightedMultiDerivative (dimension := dimension) L sigma gamma ell (index.1, 1 + index.2)
    (by unfold cartesianOrder at *; omega : cartesianOrder (index.1, 1 + index.2) + 2 ≤ grade) cell
  have actual : ∀ point : SpatialPlane, point ∈ openUnitDisk →
      HasFDerivAt (closedDiskLift (valueMap field))
        (closedDiskLift (planarDerivativeMap (firstMap field) (secondMap field)) point) point := by
    apply isClosed_property (apFiniteInto_denseRange (dimension := dimension) (grade := grade) L sigma gamma ell)
      (closedDerivativeGraph_isClosed.preimage
        (valueMap.continuous.prodMk (planarDerivativeMap_continuous.comp
          (firstMap.continuous.prodMk secondMap.continuous)))) _ field
    intro core candidate member
    change HasFDerivAt (closedDiskLift (valueMap (apFiniteInto L sigma gamma ell core)))
      (closedDiskLift (planarDerivativeMap (firstMap (apFiniteInto L sigma gamma ell core))
        (secondMap (apFiniteInto L sigma gamma ell core))) candidate) candidate
    dsimp only [valueMap, firstMap, secondMap]
    rw [apWeightedMultiDerivative_core, apWeightedMultiDerivative_core, apWeightedMultiDerivative_core,
      closedLift_value _ candidate member]
    have derivative := closedJet_multi_hasFDerivAt (apWeightedJet sigma gamma ell cell (core cell)) index candidate member
    rw [closedLift_value _ candidate member, closedLift_value _ candidate member] at derivative
    exact derivative
  have result := actual point inside
  rw [closedLift_value _ point inside] at result
  rw [closedLift_value _ point inside, closedLift_value _ point inside]
  exact result

end Grad.GaugeCoefficients.Physical.Compensated
