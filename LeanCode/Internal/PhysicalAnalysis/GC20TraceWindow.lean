import GC20ScalarEnergy

noncomputable section

namespace Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The one-sided terminal interval is chosen before the FTC estimate. -/
def traceWindow (lower frequency : ℝ) : ℝ := min (1 - lower) frequency⁻¹

theorem traceWindow_pos {lower frequency : ℝ} (lowerOne : lower < 1) (positive : 0 < frequency) :
    0 < traceWindow lower frequency :=
  lt_min (sub_pos.mpr lowerOne) (inv_pos.mpr positive)

theorem traceWindow_le_length (lower frequency : ℝ) : traceWindow lower frequency ≤ 1 - lower :=
  min_le_left _ _

theorem traceWindow_le_inverse (lower frequency : ℝ) : traceWindow lower frequency ≤ frequency⁻¹ :=
  min_le_right _ _

theorem traceWindow_inverse_bound {lower frequency : ℝ}
    (lowerOne : lower < 1) (oneLe : 1 ≤ frequency) :
    (traceWindow lower frequency)⁻¹ ≤ ((1 - lower)⁻¹ + 1) * frequency := by
  have inverseNonnegative : 0 ≤ (1 - lower)⁻¹ := (inv_pos.mpr (sub_pos.mpr lowerOne)).le
  by_cases ordered : 1 - lower ≤ frequency⁻¹
  · rw [traceWindow, min_eq_left ordered]
    exact (le_add_of_nonneg_right zero_le_one).trans
      (le_mul_of_one_le_right (by positivity) oneLe)
  · rw [traceWindow, min_eq_right (le_of_not_ge ordered), inv_inv]
    exact le_mul_of_one_le_left (zero_le_one.trans oneLe) (by linarith)

def collarTraceConstant (lower : ℝ) : ℝ := (1 - lower)⁻¹ + 2

theorem collarTraceConstant_one_le {lower : ℝ} (lowerOne : lower < 1) :
    1 ≤ collarTraceConstant lower := by
  have : 0 < (1 - lower)⁻¹ := inv_pos.mpr (sub_pos.mpr lowerOne)
  unfold collarTraceConstant
  linarith

end Grad.GaugeCoefficients.Physical.WeightedTrace
