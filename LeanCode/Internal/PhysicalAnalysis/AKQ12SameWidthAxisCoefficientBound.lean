import AKQ11LiteralCurrentAxisSpecialization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger Grad.NonlinearDivision

local instance {sigma gamma : ℝ} {grade input output : ℕ} :
    CompleteSpace (Coefficient 1 sigma gamma 1 grade input output) := by
  unfold Coefficient
  infer_instance

/-- Freeze the genuine axis value of one coefficient cell, with its
original width sigma; all newly created spatial derivatives vanish. -/
def axisFrozenCell {sigma gamma : ℝ} {grade input output : ℕ}
    (coefficient : Coefficient 1 sigma gamma 1 grade input output) (cell : ℤ) :
    Coefficient 1 sigma gamma 1 grade input output :=
  seedConstantCell 1 sigma gamma 1 grade cell
    (coefficientDerivative coefficient cell (zeroDerivativeIndexAt grade) closedOrigin)

theorem axisFrozenCell_norm_le {sigma gamma : ℝ} (admissible : Admissible 1 sigma gamma 1)
    {grade input output : ℕ} (coefficient : Coefficient 1 sigma gamma 1 grade input output) (cell : ℤ) :
    ‖axisFrozenCell coefficient cell‖ ≤ Fintype.card (DerivativeIndex grade) *
      ‖weightedDerivative coefficient cell (zeroDerivativeIndexAt grade)‖ := by
  have scale : coefficientScale 1 sigma gamma 1 grade cell (zeroDerivativeIndexAt grade) closedOrigin =
      Real.exp (sigma * |(cell : ℝ)|) * cellFrequency cell ^ grade := by
    simp [coefficientScale,originalEnvelope,scaledCellWeight,cellFrequency,Grad.CellWeights.cellWeight,
      closedOrigin,zeroDerivativeIndexAt,derivativeOrder]
  have literal := weighted_derivative_literal (L := 1) (sigma := sigma) (gamma := gamma) (ell := 1)
    grade input output coefficient cell (zeroDerivativeIndexAt grade) closedOrigin
  have normIdentity := congrArg norm literal
  rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (coefficientScale_pos 1 sigma gamma 1 grade cell _ closedOrigin).le,scale] at normIdentity
  exact (seedConstantCell_norm_le admissible cell _).trans
    (mul_le_mul_of_nonneg_left
      (normIdentity.symm.le.trans (ContinuousMap.norm_coe_le_norm _ closedOrigin))
      (Nat.cast_nonneg (Fintype.card (DerivativeIndex grade))))

theorem axisFrozenCell_norm_summable {sigma gamma : ℝ} (admissible : Admissible 1 sigma gamma 1)
    {grade input output : ℕ} (coefficient : Coefficient 1 sigma gamma 1 grade input output) :
    Summable (fun cell : ℤ => ‖axisFrozenCell coefficient cell‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (axisFrozenCell_norm_le admissible coefficient)
    ((coordinate_norm_summable coefficient.val (zeroDerivativeIndexAt grade)).mul_left _)

/-- Same-width axis restriction followed by constant spatial extension.
It is constructed inside the original completed coefficient carrier. -/
def axisFrozenCoefficient {sigma gamma : ℝ} {grade input output : ℕ}
    (coefficient : Coefficient 1 sigma gamma 1 grade input output) :
    Coefficient 1 sigma gamma 1 grade input output :=
  ∑' cell : ℤ, axisFrozenCell coefficient cell

theorem axisFrozenCoefficient_norm_le {sigma gamma : ℝ} (admissible : Admissible 1 sigma gamma 1)
    {grade input output : ℕ} (coefficient : Coefficient 1 sigma gamma 1 grade input output) :
    ‖axisFrozenCoefficient coefficient‖ ≤ Fintype.card (DerivativeIndex grade) * ‖coefficient‖ := by
  apply (norm_tsum_le_tsum_norm (axisFrozenCell_norm_summable admissible coefficient)).trans
  apply ((axisFrozenCell_norm_summable admissible coefficient).tsum_le_tsum
    (axisFrozenCell_norm_le admissible coefficient)
    ((coordinate_norm_summable coefficient.val (zeroDerivativeIndexAt grade)).mul_left _)).trans
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (coordinate_norm_sum_le coefficient.val (zeroDerivativeIndexAt grade))
    (Nat.cast_nonneg _)

theorem axisFrozenCoefficient_base_contraction {sigma gamma : ℝ} (admissible : Admissible 1 sigma gamma 1)
    {input output : ℕ} (coefficient : Coefficient 1 sigma gamma 1 0 input output) :
    ‖axisFrozenCoefficient coefficient‖ ≤ ‖coefficient‖ := by
  have card : Fintype.card (DerivativeIndex 0) = 1 := by decide
  simpa only [card,Nat.cast_one,one_mul] using axisFrozenCoefficient_norm_le admissible coefficient

end Grad.FinitePhysicalJetLift
