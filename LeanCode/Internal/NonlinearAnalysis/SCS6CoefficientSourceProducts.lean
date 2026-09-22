import SCS5MeanFreeRow

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.ConstrainedGrades Grad.AxisCore
open Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Allocation

def coefficientSourceHighConstant (parameters : PhaseParameters) (L : ℝ) (power : ℕ) : ℝ :=
  productPhaseConstant parameters power * kappaFourierConstant parameters L 0 0 * sourceDivisionConstant power L

def coefficientSourceLowConstant (parameters : PhaseParameters) (L : ℝ) (power : ℕ) : ℝ :=
  productPhaseConstant parameters power * kappaFourierConstant parameters L power 0 * sourceDivisionConstant 0 L

theorem coefficientSourceHighConstant_nonnegative (parameters : PhaseParameters) (L : ℝ) (power : ℕ) :
    0 ≤ coefficientSourceHighConstant parameters L power :=
  mul_nonneg (mul_nonneg (productPhaseConstant_pos _ _).le (kappaFourierConstant_pos _ _ _ _).le)
    (sourceDivisionConstant_nonnegative _ _)

theorem coefficientSourceLowConstant_nonnegative (parameters : PhaseParameters) (L : ℝ) (power : ℕ) :
    0 ≤ coefficientSourceLowConstant parameters L power :=
  mul_nonneg (mul_nonneg (productPhaseConstant_pos _ _).le (kappaFourierConstant_pos _ _ _ _).le)
    (sourceDivisionConstant_nonnegative _ _)

/-- Each actual cofactor-created source product, on the full completed
radial space, at the exact source p+3 and state p+5 one-high grades. -/
theorem exists_dividedCoefficientProduct {grade power : ℕ}
    (parameters : PhaseParameters) (L rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (paid : power + 3 ≤ grade)
    (source : ZAmbient parameters grade) (component : Fin 3) :
    ∃ product : DivisionRow 1 lower,
      ‖product‖ ≤ coefficientSourceHighConstant parameters L power * ‖source‖ +
        coefficientSourceLowConstant parameters L power * physicalBudget parameters field rho epsilon (power + 5) *
          ‖zLowering parameters (by omega : 3 ≤ grade) source‖ ∧
      (∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
        HasSum (fun shift : ℤ × ℤ => kappaScalar parameters L rho epsilon field small component 0 radius shift •
          originalRowCoefficient parameters 0 lower
            (dividedSourceRows (power := 0) lower positive bounded parameters L (by omega) source component)
            radius (mode - shift))
          (originalRowCoefficient parameters power lower product radius mode)) := by
  obtain ⟨product, estimate, literal⟩ := actualKappaRadialProduct parameters L rho epsilon field small
    component power 0 lower positive
    (dividedSourceRows lower positive bounded parameters L paid source component)
    (dividedSourceRows (power := 0) lower positive bounded parameters L (by omega) source component)
    (dividedSourceRows_compatible lower positive bounded parameters L paid source component)
  refine ⟨product, estimate.trans ?_, literal⟩
  have lowBudget : physicalBudget parameters field rho epsilon 5 ≤ 1 :=
    (physicalBudget_monotone parameters field rho epsilon (by omega : 5 ≤ 6)).trans
      (small.trans (min_le_left _ _))
  have highRow := dividedSourceRows_bound lower positive bounded parameters L paid source component
  have lowRow := dividedSourceRows_low_bound lower positive bounded parameters L (by omega : 3 ≤ grade) source component
  have highTerm := mul_le_mul
    (mul_le_of_le_one_right (kappaFourierConstant_pos parameters L 0 0).le lowBudget)
    highRow (norm_nonneg _) (kappaFourierConstant_pos parameters L 0 0).le
  have lowTerm := mul_le_mul_of_nonneg_left lowRow
    (mul_nonneg (kappaFourierConstant_pos parameters L power 0).le
      (physicalBudget_nonnegative parameters field rho epsilon (power + 5)))
  have combined := mul_le_mul_of_nonneg_left (add_le_add highTerm lowTerm)
    (productPhaseConstant_pos parameters power).le
  exact combined.trans_eq (by
    unfold coefficientSourceHighConstant coefficientSourceLowConstant
    ring)

end Grad.SourceCollarFullSource
