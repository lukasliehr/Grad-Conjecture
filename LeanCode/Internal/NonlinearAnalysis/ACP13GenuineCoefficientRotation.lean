import ACP12AD10Consumer
import GQ3RotationCore
import Mathlib.Analysis.Calculus.SmoothSeries

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.ActualCurrentPrimitives
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.NonlinearRange Grad.NonlinearQuotientBounds

theorem coefficientColumn_rotation_value {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (cell : ℤ) (column : PhysicalValue input) (point : ClosedDisk) :
    (rotationJet (coefficientColumnJet parameters family coherent cell column)).value point =
      (point.val 0 : ℂ) • coefficientDerivative (family 1) cell secondSpatialIndex point column -
        (point.val 1 : ℂ) • coefficientDerivative (family 1) cell firstSpatialIndex point column := by
  have first := coefficientColumnJet_derivative parameters family coherent cell column firstSpatialIndex point
  have second := coefficientColumnJet_derivative parameters family coherent cell column secondSpatialIndex point
  simp only [closedMultiDerivative, derivativeMultiIndex, firstSpatialIndex, secondSpatialIndex,
    cartesianOrder, Nat.add_zero] at first second
  have firstWord : cartesianMultiIndexWord (1, 0) = (fun _ => 0) := by
    funext position
    exact if_pos position.is_lt
  have secondWord : cartesianMultiIndexWord (0, 1) = (fun _ => 1) := by
    funext position
    exact if_neg (Nat.not_lt_zero _)
  rw [firstWord] at first
  rw [secondWord] at second
  rw [rotationJet, sub_eq_add_neg, closedJet_value_add, closedJet_value_neg,
    ContinuousMap.add_apply, ContinuousMap.neg_apply, coordinateJet_value, coordinateJet_value]
  change point.val 0 • closedDerivative (coefficientColumnJet parameters family coherent cell column) 1
    (fun _ => 1) point + -(point.val 1 • closedDerivative (coefficientColumnJet parameters family coherent cell column) 1
      (fun _ => 0) point) = _
  calc
    _ = point.val 0 • coefficientDerivative (family 1) cell secondSpatialIndex point column +
        -(point.val 1 • coefficientDerivative (family 1) cell firstSpatialIndex point column) :=
      congrArg₂ (fun a b : PhysicalValue output => point.val 0 • a + -(point.val 1 • b)) second first
    _ = _ := by simp only [Complex.coe_smul, sub_eq_add_neg]

theorem coefficientColumn_rotation_bound {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (cell : ℤ) (column : PhysicalValue input) (point : ClosedDisk) :
    ‖(rotationJet (coefficientColumnJet parameters family coherent cell column)).value point‖ ≤
      2 * coefficientCellBudget (family 1) cell * ‖column‖ := by
  have each (index : DerivativeIndex 1) :
      ‖coefficientDerivative (family 1) cell index point column‖ ≤ coefficientCellBudget (family 1) cell * ‖column‖ := by
    apply ((coefficientDerivative (family 1) cell index point).le_opNorm column).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg column)
    apply (coefficientDerivative_point_norm_le (unitDiskAdmissible parameters) (family 1) cell index point).trans
    exact Finset.single_le_sum (f := fun entry : DerivativeIndex 1 => ‖(family 1).val (cell, entry)‖)
      (fun entry _ => norm_nonneg ((family 1).val (cell, entry))) (Finset.mem_univ index)
  have coordinate (index : Fin 2) : ‖(point.val index : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real]
    exact (PiLp.norm_apply_le point.val index).trans point.property
  rw [coefficientColumn_rotation_value]
  apply (norm_sub_le _ _).trans
  have first := (norm_smul (point.val 0 : ℂ) _).le.trans
    (mul_le_mul (coordinate 0) (each secondSpatialIndex) (norm_nonneg _)
      zero_le_one)
  have second := (norm_smul (point.val 1 : ℂ) _).le.trans
    (mul_le_mul (coordinate 1) (each firstSpatialIndex) (norm_nonneg _)
      zero_le_one)
  exact (add_le_add first second).trans_eq (by ring)

end Grad.ActualCurrentPrimitives
