import AKN16OriginalFlatSourcePrimitives

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Grad.ExhaustionSourceAllocation

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarFullSource
open Grad.SourceCollarCoefficients Grad.AnnularCurrentSource Grad.GaugeCoefficients.Physical.Allocation
open Grad.AxisCore Grad.QuotientProjection

def tiltedCoefficientHighConstant (parameters : PhaseParameters) (L : ℝ) (power : ℕ) : ℝ :=
  productPhaseConstant parameters power * kappaFourierConstant parameters L 0 0 * tiltedDivisionConstant power L

def tiltedCoefficientLowConstant (parameters : PhaseParameters) (L : ℝ) (power : ℕ) : ℝ :=
  productPhaseConstant parameters power * kappaFourierConstant parameters L power 0 * tiltedDivisionConstant 0 L

theorem tiltedCoefficientHighConstant_nonnegative (parameters : PhaseParameters) (L : ℝ) (power : ℕ) :
    0 ≤ tiltedCoefficientHighConstant parameters L power :=
  mul_nonneg (mul_nonneg (productPhaseConstant_pos _ _).le (kappaFourierConstant_pos _ _ _ _).le)
    (tiltedDivisionConstant_nonnegative _ _)

theorem tiltedCoefficientLowConstant_nonnegative (parameters : PhaseParameters) (L : ℝ) (power : ℕ) :
    0 ≤ tiltedCoefficientLowConstant parameters L power :=
  mul_nonneg (mul_nonneg (productPhaseConstant_pos _ _).le (kappaFourierConstant_pos _ _ _ _).le)
    (tiltedDivisionConstant_nonnegative _ _)

theorem actualCoefficientSourceProduct_tilted_bound {grade power : ℕ}
    (parameters : PhaseParameters) (L rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (source : SmoothQuotient parameters) (flat : SourceHigherVanishing source) (paid : power + 5 ≤ grade)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (component : Fin 3) :
    ‖divisionHighWeight lower positive bounded
      (coefficientSourceProduct (power := power) parameters L rho epsilon field small lower positive bounded
        (by omega) (quotientEta parameters grade source) component)‖ ≤
      tiltedCoefficientHighConstant parameters L power * ‖quotientEta parameters grade source‖ +
        tiltedCoefficientLowConstant parameters L power * physicalBudget parameters field rho epsilon (power + 5) *
          ‖quotientEta parameters 5 source‖ := by
  have product := actualKappaProduct_tilted_bound parameters L rho epsilon field small component power 0
    lower positive bounded _ _ _
    (dividedSourceRows_compatible lower positive bounded parameters L (by omega : power + 3 ≤ grade)
      (quotientEta parameters grade source) component)
    (coefficientSourceProduct_literal parameters L rho epsilon field small lower positive bounded
      (by omega : power + 3 ≤ grade) (quotientEta parameters grade source) component)
  have lowBudget : physicalBudget parameters field rho epsilon 5 ≤ 1 :=
    (physicalBudget_monotone parameters field rho epsilon (by omega : 5 ≤ 6)).trans
      (small.trans (min_le_left _ _))
  have highRow := actualDividedSourceRows_tilted_bound parameters L source flat paid lower positive bounded component
  have lowRow := actualDividedSourceRows_tilted_low_bound parameters L source flat (by omega : 5 ≤ grade)
    lower positive bounded component
  have highTerm := mul_le_mul
    (mul_le_of_le_one_right (kappaFourierConstant_pos parameters L 0 0).le lowBudget)
    highRow (norm_nonneg _) (kappaFourierConstant_pos parameters L 0 0).le
  have lowTerm := mul_le_mul_of_nonneg_left lowRow
    (mul_nonneg (kappaFourierConstant_pos parameters L power 0).le
      (physicalBudget_nonnegative parameters field rho epsilon (power + 5)))
  have combined := mul_le_mul_of_nonneg_left (add_le_add highTerm lowTerm)
    (productPhaseConstant_pos parameters power).le
  exact product.trans (combined.trans_eq (by
    unfold tiltedCoefficientHighConstant tiltedCoefficientLowConstant
    ring))

end Grad.ExhaustionSourceAllocation
