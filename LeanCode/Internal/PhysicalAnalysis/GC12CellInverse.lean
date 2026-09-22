import GC12CellAlgebra

noncomputable section

set_option maxHeartbeats 3000000

open Grad.GenericCarriers Grad.ClosedJets Grad.GaugeCoefficients.Envelope
open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Neumann.Regularity

open Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Neumann

theorem CellFieldSummable.smul {dimension : ℕ} {field : CellField dimension}
    (summable : CellFieldSummable field) (scalar : ℂ) :
    CellFieldSummable (scalar • field) := by
  intro point
  simpa only [Pi.smul_apply, norm_smul] using
    (summable point).mul_left ‖scalar‖

theorem baseCellField_add {L sigma gamma ell : ℝ} {dimension : ℕ}
    (first second : BaseCoefficient L sigma gamma ell dimension) :
    baseCellField (first + second) = baseCellField first + baseCellField second := by
  funext cell point
  change ((coefficientScale L sigma gamma ell 0 cell zeroDerivativeIndex point : ℂ)⁻¹) •
      (first.1 (cell, zeroDerivativeIndex) point +
        second.1 (cell, zeroDerivativeIndex) point) =
    ((coefficientScale L sigma gamma ell 0 cell zeroDerivativeIndex point : ℂ)⁻¹) •
        first.1 (cell, zeroDerivativeIndex) point +
      ((coefficientScale L sigma gamma ell 0 cell zeroDerivativeIndex point : ℂ)⁻¹) •
        second.1 (cell, zeroDerivativeIndex) point
  exact smul_add _ _ _

theorem baseCellField_neg {L sigma gamma ell : ℝ} {dimension : ℕ}
    (coefficient : BaseCoefficient L sigma gamma ell dimension) :
    baseCellField (-coefficient) = -baseCellField coefficient := by
  funext cell point
  change ((coefficientScale L sigma gamma ell 0 cell zeroDerivativeIndex point : ℂ)⁻¹) •
      (-coefficient.1 (cell, zeroDerivativeIndex) point) =
    -(((coefficientScale L sigma gamma ell 0 cell zeroDerivativeIndex point : ℂ)⁻¹) •
      coefficient.1 (cell, zeroDerivativeIndex) point)
  exact smul_neg _ _

theorem baseCellField_sub {L sigma gamma ell : ℝ} {dimension : ℕ}
    (first second : BaseCoefficient L sigma gamma ell dimension) :
    baseCellField (first - second) = baseCellField first - baseCellField second := by
  rw [sub_eq_add_neg, sub_eq_add_neg, baseCellField_add, baseCellField_neg]

theorem baseCellField_identity (L sigma gamma ell : ℝ) (dimension : ℕ) :
    baseCellField (identityCoefficient L sigma gamma ell dimension) =
      identityCellField dimension := by
  funext cell point
  change coefficientValue (identityCoefficient L sigma gamma ell dimension) cell point =
    identityCellField dimension cell point
  rw [identityCoefficient_value]
  rfl

theorem baseCellField_composition {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (outer inner : BaseCoefficient L sigma gamma ell dimension) :
    baseCellField (coefficientComposition admissible 0 outer inner) =
      cellFieldComposition (baseCellField outer) (baseCellField inner) := by
  funext cell point
  exact coefficientComposition_value admissible outer inner cell point

theorem analyticCapInverseCellField_rightInverse
    {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (positive : 0 < dimension)
    (coefficient : BaseCoefficient L sigma gamma ell dimension) (theta : ℝ)
    (normBound : ‖coefficient‖ ≤ theta) (thetaLt : theta < 1) :
    cellFieldComposition
        (baseCellField (analyticCapCoefficientNeumannInverse admissible coefficient))
        (identityCellField dimension - baseCellField coefficient) =
      identityCellField dimension := by
  have rightIdentity :=
    (analyticCapCoefficientNeumannInverse_twoSidedIdentities admissible positive
      coefficient theta normBound thetaLt).2
  calc
    cellFieldComposition
        (baseCellField (analyticCapCoefficientNeumannInverse admissible coefficient))
        (identityCellField dimension - baseCellField coefficient) =
      cellFieldComposition
        (baseCellField (analyticCapCoefficientNeumannInverse admissible coefficient))
        (baseCellField (identityCoefficient L sigma gamma ell dimension - coefficient)) := by
      rw [baseCellField_sub, baseCellField_identity]
    _ = baseCellField
        (coefficientComposition admissible 0
          (analyticCapCoefficientNeumannInverse admissible coefficient)
          (identityCoefficient L sigma gamma ell dimension - coefficient)) := by
      rw [baseCellField_composition]
    _ = baseCellField (identityCoefficient L sigma gamma ell dimension) := by
      rw [rightIdentity]
    _ = identityCellField dimension :=
      baseCellField_identity L sigma gamma ell dimension

/-- Solve `X = H X + R` by the already constructed right inverse of `I-H`.
All reassociations are justified by absolute cell summability. -/
theorem cellField_fixedPoint_solution {dimension : ℕ}
    {inverse coefficient unknown forcing : CellField dimension}
    (inverseSummable : CellFieldSummable inverse)
    (coefficientSummable : CellFieldSummable coefficient)
    (unknownSummable : CellFieldSummable unknown)
    (_forcingSummable : CellFieldSummable forcing)
    (rightInverse : cellFieldComposition inverse
      (identityCellField dimension - coefficient) = identityCellField dimension)
    (fixedPoint : unknown =
      cellFieldComposition coefficient unknown + forcing) :
    unknown = cellFieldComposition inverse forcing := by
  have identitySummable := identityCellField_summable dimension
  have differenceSummable := identitySummable.sub coefficientSummable
  have compositionSummable := coefficientSummable.composition unknownSummable
  have residual :
      cellFieldComposition (identityCellField dimension - coefficient) unknown =
        forcing := by
    calc
      cellFieldComposition (identityCellField dimension - coefficient) unknown =
          cellFieldComposition (identityCellField dimension) unknown -
            cellFieldComposition coefficient unknown :=
        cellFieldComposition_sub_outer identitySummable coefficientSummable
          unknownSummable
      _ = unknown - cellFieldComposition coefficient unknown := by
        rw [cellFieldComposition_identity_left unknownSummable]
      _ = forcing := by
        rw [sub_eq_iff_eq_add]
        simpa only [add_comm] using fixedPoint
  calc
    unknown = cellFieldComposition (identityCellField dimension) unknown :=
      (cellFieldComposition_identity_left unknownSummable).symm
    _ = cellFieldComposition
        (cellFieldComposition inverse
          (identityCellField dimension - coefficient)) unknown := by
      rw [rightInverse]
    _ = cellFieldComposition inverse
        (cellFieldComposition (identityCellField dimension - coefficient) unknown) :=
      cellFieldComposition_associative inverseSummable differenceSummable
        unknownSummable
    _ = cellFieldComposition inverse forcing := by rw [residual]

end Grad.GaugeCoefficients.Neumann.Regularity
