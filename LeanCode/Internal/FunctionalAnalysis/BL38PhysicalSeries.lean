import BL37Summability

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

/-- The iterated angular/cell sum of the literal N24 summand equals the
actual double-mode sum, by absolute summability. -/
theorem boundaryLiftSummand_exchange {dimension : ℕ} (parameters : PhaseParameters)
    (values : BoundaryCore parameters dimension) (time : ℝ) (timeNonneg : 0 ≤ time)
    (angle cellPoint : CellCircle) :
    ∑' cell : ℤ, ∑' mode : ℤ, boundaryLiftSummand values.1 time angle cellPoint (mode, cell) =
      ∑' mode : ℤ × ℤ, boundaryLiftSummand values.1 time angle cellPoint mode := by
  have summandSummable := boundaryLiftSummand_summable parameters values time timeNonneg angle cellPoint
  have swappedSummable : Summable (fun pair : ℤ × ℤ =>
      boundaryLiftSummand values.1 time angle cellPoint (pair.2, pair.1)) :=
    (Equiv.prodComm ℤ ℤ).summable_iff.mpr summandSummable
  have iterated : (∑' pair : ℤ × ℤ, boundaryLiftSummand values.1 time angle cellPoint (pair.2, pair.1)) =
      ∑' cell : ℤ, ∑' mode : ℤ, boundaryLiftSummand values.1 time angle cellPoint (mode, cell) :=
    swappedSummable.tsum_prod
  have swapTsum : (∑' pair : ℤ × ℤ, boundaryLiftSummand values.1 time angle cellPoint (pair.2, pair.1)) =
      ∑' mode : ℤ × ℤ, boundaryLiftSummand values.1 time angle cellPoint mode :=
    (Equiv.prodComm ℤ ℤ).tsum_eq (fun mode => boundaryLiftSummand values.1 time angle cellPoint mode)
  exact iterated.symm.trans swapTsum

/-- The actual original physical double-series identity: the physical value
of the common lift on the literal polar collar equals the literal N24
double-Fourier exponential formula. -/
theorem boundaryLift_physical_value {dimension : ℕ} (parameters : PhaseParameters)
    (values : BoundaryCore parameters dimension) (point : ClosedDisk) (time : ℝ)
    (timeNonneg : 0 ≤ time) (timeLe : time ≤ (1 / 4 : ℝ)) (angle cellPoint : CellCircle)
    (pointLaw : point.val = (1 - time) • boundaryCirclePoint angle) :
    (originalPhysicalClosedJet parameters (boundaryLift parameters values)).value (point, cellPoint) =
      literalBoundaryLift values.1 time angle cellPoint := by
  classical
  have reconstruction : (originalPhysicalClosedJet parameters (boundaryLift parameters values)).value
      (point, cellPoint) =
      ∑' cell : ℤ, cellCharacter cell cellPoint • ((boundaryLift parameters values).1 cell).value point := by
    rw [originalPhysicalClosedJet, ordinaryReconstructedClosedJet_value, ordinaryReconstructedValue_apply]
    simp only [originalCoefficientCore_apply]
  have termLaw : ∀ cell : ℤ,
      cellCharacter cell cellPoint • ((boundaryLift parameters values).1 cell).value point =
        collarCutoff1D time • ∑' mode : ℤ, boundaryLiftSummand values.1 time angle cellPoint (mode, cell) := by
    intro cell
    rw [boundaryLift_literal_cell parameters values cell point time timeLe angle pointLaw]
    unfold literalBoundaryCell
    rw [smul_comm (cellCharacter cell cellPoint) (collarCutoff1D time)]
    congr 1
    rw [← tsum_const_smul'' (cellCharacter cell cellPoint)]
    apply tsum_congr
    intro mode
    simp only [boundaryLiftSummand, cellCharacter]
    rw [smul_smul]
    congr 1
    ring
  rw [reconstruction, tsum_congr termLaw, tsum_const_smul'' (collarCutoff1D time)]
  unfold literalBoundaryLift
  rw [boundaryLiftSummand_exchange parameters values time timeNonneg angle cellPoint]

end Grad.BoundaryLift
