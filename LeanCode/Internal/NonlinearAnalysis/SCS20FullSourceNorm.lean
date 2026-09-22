import SCS19G3ValueRealization

noncomputable section

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarBulk Grad.AxisCore Grad.GaugeCoefficients.Physical.Allocation Grad.ConstrainedGrades

/-- Literal AH source graph: S11(F0), S10(RF0), S10(F2), S00(G3), S00(RG3).
All five coordinates retain the original radial/analytic/frequency norms. -/
def fullSourceNorm (parameters : PhaseParameters) (L rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (order : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (source : ZAmbient parameters (order + 4)) : ℝ :=
  ‖completedForceS11 lower positive bounded parameters order (zLowering parameters (by omega) source)‖ +
  ‖completedForceAngular lower positive bounded parameters order (zLowering parameters (by omega) source)‖ +
  ‖completedFourthSource lower positive bounded parameters L order (zLowering parameters (by omega) source)‖ +
  ‖g3ValueRow parameters L rho epsilon field small lower positive bounded (le_refl _) source‖ +
  ‖g3AngularRow parameters L rho epsilon field small lower positive bounded (le_refl _) source‖

def fullSourceHighConstant (parameters : PhaseParameters) (L : ℝ) (order : ℕ) : ℝ :=
  3 * sourceBulkConstant L order + 2 * g3HighConstant parameters L order

def fullSourceLowConstant (parameters : PhaseParameters) (L : ℝ) (order : ℕ) : ℝ :=
  2 * g3LowConstant parameters L order

theorem fullSourceLowConstant_nonnegative (parameters : PhaseParameters) (L : ℝ) (order : ℕ) :
    0 ≤ fullSourceLowConstant parameters L order := by
  unfold fullSourceLowConstant g3LowConstant
  exact mul_nonneg (by norm_num) (mul_nonneg (by norm_num) (coefficientSourceLowConstant_nonnegative parameters L _))

theorem fullSourceNorm_bound (parameters : PhaseParameters) (L rho epsilon : ℝ) (LPositive : 0 < L)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (order : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (source : ZAmbient parameters (order + 4)) :
    fullSourceNorm parameters L rho epsilon field small order lower positive bounded source ≤
      fullSourceHighConstant parameters L order * ‖source‖ +
      fullSourceLowConstant parameters L order * physicalBudget parameters field rho epsilon (order + 6) *
        ‖zLowering parameters (by omega : 3 ≤ order + 4) source‖ := by
  have lowered := zLowering_norm_le parameters (by omega : order + 2 ≤ order + 4) source
  have first := (completedForceS11_bound lower positive bounded parameters order
    (zLowering parameters (by omega) source)).trans
      (mul_le_mul_of_nonneg_left lowered (planarBulkConstant_nonnegative order))
  have second := (completedForceAngular_bound lower positive bounded parameters order
    (zLowering parameters (by omega) source)).trans
      (mul_le_mul_of_nonneg_left lowered (planarBulkConstant_nonnegative order))
  have third := (completedFourthSource_bound lower positive bounded parameters L LPositive order
    (zLowering parameters (by omega) source)).trans
      (mul_le_mul_of_nonneg_left lowered (mul_nonneg (inv_nonneg.mpr LPositive.le)
        (Grad.SourceCollarRestriction.restrictionGraphConstant_nonnegative order 1)))
  have bulkConstant : planarBulkConstant order ≤ sourceBulkConstant L order := by
    unfold sourceBulkConstant
    have nonnegative := planarBulkConstant_nonnegative order
    have fourthNonnegative := mul_nonneg (inv_nonneg.mpr LPositive.le)
      (Grad.SourceCollarRestriction.restrictionGraphConstant_nonnegative order 1)
    linarith only [nonnegative, fourthNonnegative]
  have fourthConstant : L⁻¹ * Grad.SourceCollarRestriction.restrictionGraphConstant order 1 ≤ sourceBulkConstant L order := by
    unfold sourceBulkConstant
    linarith only [planarBulkConstant_nonnegative order]
  have high := g3ValueRow_bound parameters L rho epsilon field small lower positive bounded (le_refl _) source
  have angular := g3AngularRow_bound parameters L rho epsilon field small lower positive bounded (le_refl _) source
  have first' := first.trans (mul_le_mul_of_nonneg_right bulkConstant (norm_nonneg source))
  have second' := second.trans (mul_le_mul_of_nonneg_right bulkConstant (norm_nonneg source))
  have third' := third.trans (mul_le_mul_of_nonneg_right fourthConstant (norm_nonneg source))
  unfold fullSourceNorm fullSourceHighConstant fullSourceLowConstant
  linarith only [first', second', third', high, angular]

end Grad.SourceCollarFullSource
