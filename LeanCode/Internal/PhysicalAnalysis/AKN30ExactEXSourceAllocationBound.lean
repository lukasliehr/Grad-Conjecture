import AKN29ActualWeightedSourceNorm

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Grad.ExhaustionSourceAllocation
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.SourceCollarFullSource Grad.SourceCollarCoefficients Grad.AnnularCurrentSource
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection Grad.ConstrainedGrades
open Grad.SourceCollarBulk Grad.AnnularStrongData Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularExhaustionEstimate

theorem originalSourceNorm_monotone (parameters : PhaseParameters) (source : SmoothQuotient parameters) :
    Monotone (fun grade => ‖quotientEta parameters grade source‖) := by
  intro first second ordered
  have bound := zLowering_norm_le parameters ordered (quotientEta parameters second source)
  rw [zLowering_core] at bound
  exact bound

private theorem fourTerm_uniform {a b c d x y z w budget X W B : ℝ}
    (x0 : 0 ≤ x) (y0 : 0 ≤ y) (z0 : 0 ≤ z) (w0 : 0 ≤ w) (budget0 : 0 ≤ budget)
    (X0 : 0 ≤ X) (W0 : 0 ≤ W) (B0 : 0 ≤ B)
    (xBound : x ≤ X) (yBound : y ≤ X) (zBound : z ≤ X) (wBound : w ≤ W) (budgetBound : budget ≤ B) :
    a * x + b * y + c * z + d * budget * w ≤
      (1 + |a| + |b| + |c| + |d|) * (X + B * W) := by
  have first := (mul_le_mul_of_nonneg_right (le_abs_self a) x0).trans
    (mul_le_mul_of_nonneg_left xBound (abs_nonneg a))
  have second := (mul_le_mul_of_nonneg_right (le_abs_self b) y0).trans
    (mul_le_mul_of_nonneg_left yBound (abs_nonneg b))
  have third := (mul_le_mul_of_nonneg_right (le_abs_self c) z0).trans
    (mul_le_mul_of_nonneg_left zBound (abs_nonneg c))
  have product := (mul_le_mul_of_nonneg_right budgetBound w0).trans
    (mul_le_mul_of_nonneg_left wBound B0)
  have fourth := (mul_le_mul_of_nonneg_right (le_abs_self d) (mul_nonneg budget0 w0)).trans
    (mul_le_mul_of_nonneg_left product (abs_nonneg d))
  have upper := add_le_add (add_le_add (add_le_add first second) third) fourth
  have extra0 : 0 ≤ (1 + |a| + |b| + |c|) * (B * W) := by positivity
  have extra1 : 0 ≤ (1 + |d|) * X := by positivity
  nlinarith only [upper, extra0, extra1]

/-- Fixed coefficient/source allocation constant, independent of the annular
lower endpoint and of the source and state. Original analytic width is unchanged. -/
def originalSourceAllocationConstant (parameters : PhaseParameters) (L : ℝ) (grade : ℕ) : ℝ :=
  1 + |3 * tiltedForceConstant (grade + 1) + 2 * tiltedG3HighConstant parameters L (grade + 1)| +
    |(|L⁻¹| * Real.sqrt (remainderAngularBoundConstant 3 grade 0))| +
    |planarBulkConstant grade + L⁻¹ * restrictionGraphConstant grade 1| +
    |6 * tiltedCoefficientLowConstant parameters L (grade + 1)|

theorem originalSourceAllocationConstant_positive (parameters : PhaseParameters) (L : ℝ) (grade : ℕ) :
    0 < originalSourceAllocationConstant parameters L grade := by
  unfold originalSourceAllocationConstant
  positivity

/-- Exact EX source payment on the actual independent original datum:
F_(t+8) + B_(t+14) F_8, uniformly for every moving inner radius. Both original
AH graphs, the full G3 and RG3, and every copied source are retained. -/
theorem actualOriginalSourceDatum_EX_bound (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (lengthPositive : 0 < L) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (grade : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (source : SmoothQuotient parameters) (flat : IsFlat source) (vanishing : SourceHigherVanishing source) :
    originalWeightedDatumNorm parameters lower L positive bounded.le lengthPositive
      (actualOriginalSourceDatum parameters L rho epsilon field small lower positive bounded grade source flat) ≤
      originalSourceAllocationConstant parameters L grade *
        (‖quotientEta parameters (grade + 8) source‖ +
          physicalBudget parameters field rho epsilon (grade + 14) * ‖quotientEta parameters 8 source‖) := by
  have raw := actualOriginalSourceDatum_weighted_bound parameters L rho epsilon lengthPositive field small
    lower positive bounded grade source flat vanishing
  have estimate := fourTerm_uniform
    (a := 3 * tiltedForceConstant (grade + 1) + 2 * tiltedG3HighConstant parameters L (grade + 1))
    (b := |L⁻¹| * Real.sqrt (remainderAngularBoundConstant 3 grade 0))
    (c := planarBulkConstant grade + L⁻¹ * restrictionGraphConstant grade 1)
    (d := 6 * tiltedCoefficientLowConstant parameters L (grade + 1))
    (norm_nonneg (quotientEta parameters (grade + 6) source))
    (norm_nonneg (quotientEta parameters (grade + 5) source))
    (norm_nonneg (quotientEta parameters (grade + 2) source))
    (norm_nonneg (quotientEta parameters 5 source))
    (physicalBudget_nonnegative parameters field rho epsilon (grade + 6))
    (norm_nonneg (quotientEta parameters (grade + 8) source))
    (norm_nonneg (quotientEta parameters 8 source))
    (physicalBudget_nonnegative parameters field rho epsilon (grade + 14))
    (originalSourceNorm_monotone parameters source (by omega : grade + 6 ≤ grade + 8))
    (originalSourceNorm_monotone parameters source (by omega : grade + 5 ≤ grade + 8))
    (originalSourceNorm_monotone parameters source (by omega : grade + 2 ≤ grade + 8))
    (originalSourceNorm_monotone parameters source (by norm_num : 5 ≤ 8))
    (physicalBudget_monotone parameters field rho epsilon (by omega : grade + 6 ≤ grade + 14))
  unfold originalSourceAllocationConstant
  linarith only [raw, estimate]

theorem actualOriginalSourceDatum_base_bound (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (lengthPositive : 0 < L) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (M : ℝ) (stateBound : physicalBudget parameters field rho epsilon 14 ≤ M)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (source : SmoothQuotient parameters) (flat : IsFlat source) (vanishing : SourceHigherVanishing source) :
    originalWeightedDatumNorm parameters lower L positive bounded.le lengthPositive
      (actualOriginalSourceDatum parameters L rho epsilon field small lower positive bounded 0 source flat) ≤
      originalSourceAllocationConstant parameters L 0 * (1 + M) * ‖quotientEta parameters 8 source‖ := by
  have estimate := actualOriginalSourceDatum_EX_bound parameters L rho epsilon lengthPositive field small
    0 lower positive bounded source flat vanishing
  have product := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right stateBound (norm_nonneg (quotientEta parameters 8 source)))
    (originalSourceAllocationConstant_positive parameters L 0).le
  norm_num only [Nat.zero_add] at estimate
  nlinarith only [estimate, product]

end Grad.ExhaustionSourceAllocation
