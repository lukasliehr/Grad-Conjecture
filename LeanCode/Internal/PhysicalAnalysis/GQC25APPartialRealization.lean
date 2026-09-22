import GQC24APPartial

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope

theorem apTrace_hasFDerivAt {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension grade : ℕ} (large : 2 ≤ grade) (cell : ℤ)
    (field : apGrade L sigma gamma ell dimension (grade + 1)) (point : SpatialPlane) (inside : point ∈ openUnitDisk) :
    HasFDerivAt (closedDiskLift (apTrace admissible (large.trans (Nat.le_succ grade)) cell field))
      (planarDerivative
        (closedDiskLift (apTrace admissible large cell (apPartial admissible dimension grade 0 field)) point)
        (closedDiskLift (apTrace admissible large cell (apPartial admissible dimension grade 1 field)) point)) point := by
  let valueMap := apTrace (dimension := dimension) admissible (large.trans (Nat.le_succ grade)) cell
  let firstMap := (apTrace admissible large cell).comp (apPartial admissible dimension grade 0)
  let secondMap := (apTrace admissible large cell).comp (apPartial admissible dimension grade 1)
  have actual : ∀ candidate : SpatialPlane, candidate ∈ openUnitDisk →
      HasFDerivAt (closedDiskLift (valueMap field))
        (closedDiskLift (planarDerivativeMap (firstMap field) (secondMap field)) candidate) candidate := by
    apply isClosed_property (apFiniteInto_denseRange (dimension := dimension) (grade := grade + 1) L sigma gamma ell)
      (closedDerivativeGraph_isClosed.preimage
        (valueMap.continuous.prodMk (planarDerivativeMap_continuous.comp
          (firstMap.continuous.prodMk secondMap.continuous)))) _ field
    intro core candidate member
    change HasFDerivAt (closedDiskLift (apTrace admissible (large.trans (Nat.le_succ grade)) cell (apFiniteInto L sigma gamma ell core)))
      (closedDiskLift (planarDerivativeMap
        (apTrace admissible large cell (apPartial admissible dimension grade 0 (apFiniteInto L sigma gamma ell core)))
        (apTrace admissible large cell (apPartial admissible dimension grade 1 (apFiniteInto L sigma gamma ell core)))) candidate) candidate
    rw [apTrace_core, apPartial_core, apPartial_core, apTrace_core, apTrace_core,
      closedLift_value _ candidate member]
    have derivative := closedJet_first (core cell) candidate member
    rw [closedLift_value _ candidate member, closedLift_value _ candidate member] at derivative
    exact derivative
  have result := actual point inside
  rw [closedLift_value _ point inside] at result
  rw [closedLift_value _ point inside, closedLift_value _ point inside]
  exact result

/-- The completed derivative is the genuine derivative of the reconstructed
smooth closed coefficient, not just a bounded operator with a formal core law. -/
theorem apSmoothPartial_jet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (field : APSmooth L sigma gamma ell dimension) (coordinate : Fin 2) (cell : ℤ) :
    apSmoothJet admissible dimension cell (apSmoothPartial admissible dimension coordinate field) =
      partialJet coordinate (apSmoothJet admissible dimension cell field) := by
  apply closedJet_eq_of_value_eq
  apply continuousMap_eq_of_openDisk
  intro point inside
  change (apFamilyJet (apSmoothPartial admissible dimension coordinate field).val
    (apSmoothPartial admissible dimension coordinate field).property cell).value point = _
  rw [apFamilyJet_value_trace admissible (apSmoothPartial admissible dimension coordinate field).val
    (apSmoothPartial admissible dimension coordinate field).property (by omega : 2 ≤ 2) cell,
    partialJet_value_fderiv coordinate _ point inside]
  change apTrace admissible (by omega : 2 ≤ 2) cell
    (apPartial admissible dimension 2 coordinate (field.val 3)) point =
      fderiv ℝ (closedDiskLift (apFamilyJet field.val field.property cell).value) point.val (spatialBasis coordinate)
  rw [apFamilyJet_value_trace admissible field.val field.property (by omega : 2 ≤ 3) cell,
    (apTrace_hasFDerivAt admissible (by omega : 2 ≤ 2) cell (field.val 3) point.val inside).fderiv,
    planarDerivative_basis]
  fin_cases coordinate <;> simp only [Fin.zero_eta, Fin.isValue]
  · exact (closedLift_value _ point.val inside).symm
  · exact (closedLift_value _ point.val inside).symm

end Grad.GaugeCoefficients.Physical.Compensated
