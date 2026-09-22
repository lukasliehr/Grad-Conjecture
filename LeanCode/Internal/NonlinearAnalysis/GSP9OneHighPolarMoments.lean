import GSP8PolarRowAlgebra

noncomputable section
open scoped BigOperators
namespace Grad.ActualGaugeSigmaPrimitives
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollarDivision
open Grad.ActualCurrentPrimitives Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.Allocation

/-- Constants depend only on the coefficient profile and fixed grades, not the state. -/
def physicalPolarEntryConstant (profile : ℕ → ℝ) (row column : Fin 3) (tangential radial : ℕ) : ℝ :=
  polarEntryConstant row column tangential radial * |profile (tangential + radial + 1)|

theorem physicalPolarEntryConstant_nonnegative (profile : ℕ → ℝ) (row column : Fin 3) (tangential radial : ℕ) :
    0 ≤ physicalPolarEntryConstant profile row column tangential radial :=
  mul_nonneg (polarEntryConstant_pos row column tangential radial).le (abs_nonneg _)

theorem physicalPolarEntryScalarMoment_bound (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3) (coherent : FamilyCoherent family)
    (field : ACore parameters 3) (rho epsilon : ℝ) (profile : ℕ → ℝ)
    (normBound : ∀ grade, ‖family grade‖ ≤ profile grade * physicalBudget parameters field rho epsilon (4 + grade))
    (row column : Fin 3) (tangential radial : ℕ) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    (∑' mode, productMoment parameters tangential radius
      (polarEntryScalar parameters family coherent row column radial radius) mode) ≤
      physicalPolarEntryConstant profile row column tangential radial *
        physicalBudget parameters field rho epsilon (tangential + radial + 5) := by
  have first := polarEntryScalarMoment_bound parameters family coherent row column tangential radial radius nonnegative bounded
  have high := normBound (tangential + radial + 1)
  have absolute := mul_le_mul_of_nonneg_right (le_abs_self (profile (tangential + radial + 1)))
    (physicalBudget_nonnegative parameters field rho epsilon (4 + (tangential + radial + 1)))
  have total := first.trans (mul_le_mul_of_nonneg_left (high.trans absolute)
    (polarEntryConstant_pos row column tangential radial).le)
  simpa only [physicalPolarEntryConstant, ← mul_assoc,
    show 4 + (tangential + radial + 1) = tangential + radial + 5 by omega] using total

theorem physicalRotatedPolarEntryScalarMoment_bound (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3) (coherent : FamilyCoherent family)
    (field : ACore parameters 3) (rho epsilon : ℝ) (profile : ℕ → ℝ)
    (normBound : ∀ grade, ‖family grade‖ ≤ profile grade * physicalBudget parameters field rho epsilon (4 + grade))
    (row column : Fin 3) (tangential radial : ℕ) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Summable (productMoment parameters tangential radius
      (angularCoefficientSequence (polarEntryScalar parameters family coherent row column radial radius))) ∧
    (∑' mode, productMoment parameters tangential radius
      (angularCoefficientSequence (polarEntryScalar parameters family coherent row column radial radius)) mode) ≤
      physicalPolarEntryConstant profile row column (tangential + 1) radial *
        physicalBudget parameters field rho epsilon (tangential + radial + 6) := by
  have summable := polarEntryScalarMoment_summable parameters family coherent row column (tangential + 1) radial radius nonnegative bounded
  refine ⟨angularCoefficientSequence_moment_summable parameters tangential radius _ summable, ?_⟩
  apply (angularCoefficientSequence_moment_bound parameters tangential radius _ summable).trans
  have bound := physicalPolarEntryScalarMoment_bound parameters family coherent field rho epsilon profile normBound
    row column (tangential + 1) radial radius nonnegative bounded
  simpa only [show tangential + 1 + radial + 5 = tangential + radial + 6 by omega] using bound

end Grad.ActualGaugeSigmaPrimitives

