import SCS20FullSourceNorm

noncomputable section

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollarRestriction
open Grad.SourceCollarBulk Grad.AxisCore Grad.GaugeCoefficients.Physical.Allocation Grad.ConstrainedGrades

theorem g3HighConstant_nonnegative (parameters : PhaseParameters) (L : ℝ) (order : ℕ) :
    0 ≤ g3HighConstant parameters L order := by
  unfold g3HighConstant
  exact add_nonneg (add_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
    (mul_nonneg (by norm_num) (coefficientSourceHighConstant_nonnegative parameters L _)))
    (sourceDivisionConstant_nonnegative _ _)

theorem fullSourceHighConstant_positive (parameters : PhaseParameters) (L : ℝ) (LPositive : 0 < L)
    (order : ℕ) : 0 < fullSourceHighConstant parameters L order := by
  unfold fullSourceHighConstant
  exact add_pos_of_pos_of_nonneg (mul_pos (by norm_num) (sourceBulkConstant_positive L LPositive order))
    (mul_nonneg (by norm_num) (g3HighConstant_nonnegative parameters L order))

def fullSourceBaseConstant (parameters : PhaseParameters) (L : ℝ) : ℝ :=
  fullSourceHighConstant parameters L 0 + fullSourceLowConstant parameters L 0

theorem fullSourceBaseConstant_positive (parameters : PhaseParameters) (L : ℝ) (LPositive : 0 < L) :
    0 < fullSourceBaseConstant parameters L :=
  add_pos_of_pos_of_nonneg (fullSourceHighConstant_positive parameters L LPositive 0)
    (fullSourceLowConstant_nonnegative parameters L 0)

/-- The independent G4 base estimate. No higher state norm is substituted
into itself, and the coefficient hypothesis is the SAME fixed B6 ball. -/
theorem fullSourceNorm_base (parameters : PhaseParameters) (L rho epsilon : ℝ) (LPositive : 0 < L)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (source : ZAmbient parameters 4) :
    fullSourceNorm parameters L rho epsilon field small 0 lower positive bounded source ≤
      fullSourceBaseConstant parameters L * ‖source‖ := by
  have estimate := fullSourceNorm_bound parameters L rho epsilon LPositive field small 0 lower positive bounded source
  have coefficientLow : physicalBudget parameters field rho epsilon 6 ≤ 1 := small.trans (min_le_left _ _)
  have sourceLow := zLowering_norm_le parameters (by norm_num : 3 ≤ 4) source
  have product : physicalBudget parameters field rho epsilon 6 *
      ‖zLowering parameters (by norm_num : 3 ≤ 4) source‖ ≤ ‖source‖ := by
    simpa only [one_mul] using mul_le_mul coefficientLow sourceLow (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have allocated := mul_le_mul_of_nonneg_left product (fullSourceLowConstant_nonnegative parameters L 0)
  unfold fullSourceBaseConstant
  linarith only [estimate, allocated]

end Grad.SourceCollarFullSource
