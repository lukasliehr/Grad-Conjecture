import AKCB1OrderedIdentityAllocation
import AKBH1GenericMomentMultiplier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.RadialLedger

theorem startupReserveRatio_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {reserve weight : ℕ} (bound : reserve ≤ weight)
    (cell : ℤ) :
    |scaledCellWeight L ell cell ^ reserve / Grad.CellWeights.cellWeight cell ^ weight| ≤ 1 := by
  have positive := Grad.CellWeights.cellWeight_pos cell
  rw [abs_of_nonneg (div_nonneg (pow_nonneg (zero_le_one.trans (scaledCellWeight_one_le L ell cell)) _) (pow_nonneg positive.le _))]
  apply (div_le_one (pow_pos positive _)).mpr
  exact (pow_le_pow_left₀ ((scaledCellWeight_one_le L ell cell).trans' zero_le_one)
    (scaledCellWeight_le_frequency admissible cell) reserve).trans
      (pow_le_pow_right₀ (Grad.CellWeights.cellWeight_one_le cell) bound)

/-- Restore the input frequency reserve using an already stored weighted
jet coordinate. Spatial order is unchanged. -/
def startupReservedDerivative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension order weight reserve : ℕ}
    (bound : reserve ≤ weight) (index : JetIndex order)
    (jet : GraphGrade dimension order weight openUnitDisk) : StartupL2 dimension :=
  startupMomentDiagonalField (fun cell _ => scaledCellWeight L ell cell ^ reserve / Grad.CellWeights.cellWeight cell ^ weight)
    1 zero_le_one (fun cell _ => startupReserveRatio_bound admissible bound cell)
    (fun _ => aestronglyMeasurable_const) (jet.val index)

theorem startupReservedDerivative_ae {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension order weight reserve : ℕ}
    (bound : reserve ≤ weight) (index : JetIndex order)
    (jet : GraphGrade dimension order weight openUnitDisk) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      startupReservedDerivative admissible bound index jet point cell =
        ((scaledCellWeight L ell cell ^ reserve : ℝ) : ℂ) •
          Realization.recoveredDerivative dimension order openUnitDisk (fun _ => weight) index jet point cell := by
  filter_upwards [startupMomentDiagonalField_ae
    (fun cell _ => scaledCellWeight L ell cell ^ reserve / Grad.CellWeights.cellWeight cell ^ weight)
    1 zero_le_one (fun cell _ => startupReserveRatio_bound admissible bound cell)
    (fun _ => aestronglyMeasurable_const) (jet.val index),
    Realization.recoveredDerivative_coordinates dimension order openUnitDisk (fun _ => weight) index jet] with point stored recovered
  intro cell
  change startupReservedDerivative admissible bound index jet point cell = _
  rw [show startupReservedDerivative admissible bound index jet point cell = _ from stored cell,recovered cell,smul_smul]
  simp only [div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_pow,Grad.CellWeights.inverseFactor]

theorem startupReservedDerivative_norm {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension order weight reserve : ℕ}
    (bound : reserve ≤ weight) (index : JetIndex order)
    (jet : GraphGrade dimension order weight openUnitDisk) :
    ‖startupReservedDerivative admissible bound index jet‖ ≤ ‖jet‖ := by
  have bounded := startupMomentDiagonalField_norm
    (fun cell _ => scaledCellWeight L ell cell ^ reserve / Grad.CellWeights.cellWeight cell ^ weight)
    1 zero_le_one (fun cell _ => startupReserveRatio_bound admissible bound cell)
    (fun _ => aestronglyMeasurable_const) (jet.val index)
  exact (bounded.trans_eq (one_mul _)).trans (PiLp.norm_apply_le jet.val index)

theorem startupReservedDerivative_projection {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension order weight reserve : ℕ}
    (bound : reserve ≤ weight) (index : JetIndex order)
    (jet : GraphGrade dimension order weight openUnitDisk) (cell : ℤ) :
    fieldCellProjection dimension openUnitDisk cell (startupReservedDerivative admissible bound index jet) =
      ((scaledCellWeight L ell cell ^ reserve : ℝ) : ℂ) •
        fieldCellProjection dimension openUnitDisk cell
          (Realization.recoveredDerivative dimension order openUnitDisk (fun _ => weight) index jet) := by
  apply Lp.ext
  filter_upwards [startupReservedDerivative_ae admissible bound index jet,
    fieldCellProjection_ae dimension openUnitDisk (startupReservedDerivative admissible bound index jet),
    fieldCellProjection_ae dimension openUnitDisk
      (Realization.recoveredDerivative dimension order openUnitDisk (fun _ => weight) index jet),
    Lp.coeFn_smul ((scaledCellWeight L ell cell ^ reserve : ℝ) : ℂ)
      (fieldCellProjection dimension openUnitDisk cell
        (Realization.recoveredDerivative dimension order openUnitDisk (fun _ => weight) index jet))]
    with point restored left right scaled
  rw [scaled,Pi.smul_apply,left cell,right cell]
  exact restored cell

end Grad.CartesianStartup
