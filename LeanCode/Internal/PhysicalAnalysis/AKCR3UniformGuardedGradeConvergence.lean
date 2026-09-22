import AKCR2ActualGuardedNewtonSmoothLimit
import Mathlib.Analysis.Normed.Group.FunctionSeries

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Filter
open scoped Topology BigOperators

namespace Grad.NashMoser.OriginalLimit
open Grad.NashMoser.Numeric

/-- Numerical all-order decay gives uniform convergence of the SAME guarded
iterates in each complete grade on the unchanged parameter set. -/
theorem uniformGuardedGradeConvergence
    {Parameter E F G : Type*} [Nonempty Parameter]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedAddCommGroup G] [CompleteSpace G]
    {initial radius highConstant quadratic : ℝ} {smoothing : ℕ → ℝ} {loss : ℕ}
    (data : Parameter → GuardedNewtonData E F initial radius highConstant quadratic smoothing loss)
    (gradeMap : E →+ G) (grade constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ point index,
      ‖(data point).gradeCorrection gradeMap index‖ ≤
        constant * newtonTime initial index ^ grade * ‖(data point).mapping ((data point).iterate index)‖) :
    TendstoUniformly (fun index point => gradeMap ((data point).iterate index))
      (fun point => (data point).gradeLimit gradeMap) atTop := by
  let sample := data (Classical.choice (inferInstance : Nonempty Parameter))
  have lossLarge : (1 : ℝ) ≤ loss := by exact_mod_cast sample.lossLarge
  obtain ⟨order, gap⟩ := ((tendsto_atTop.1 (bootstrapExponent_tendsto lossLarge)) (grade + 2)).exists
  let decay := bootstrapConstant initial loss quadratic smoothing order
  let exponent := bootstrapExponent loss order - grade
  have exponentLarge : 2 ≤ exponent := by dsimp [exponent]; linarith
  have majorant : Summable (fun index : ℕ => constant * decay * newtonTime initial index ^ (-exponent)) := by
    simpa only [zero_add] using (newtonTime_tail sample.initialLarge exponentLarge 0).1.mul_left (constant * decay)
  have paid (index : ℕ) (point : Parameter) :
      ‖(data point).gradeCorrection gradeMap index‖ ≤ constant * decay * newtonTime initial index ^ (-exponent) := by
    have positive := newtonTime_pos (by linarith [sample.initialLarge] : 0 < initial) index
    calc
      _ ≤ constant * newtonTime initial index ^ grade * ‖(data point).mapping ((data point).iterate index)‖ := bounded point index
      _ ≤ constant * newtonTime initial index ^ grade *
          (decay * newtonTime initial index ^ (-bootstrapExponent loss order)) :=
        mul_le_mul_of_nonneg_left ((data point).iterate_allOrdersDecay order index)
          (mul_nonneg nonnegative (Real.rpow_nonneg positive.le _))
      _ = _ := by
        dsimp [exponent]
        rw [show -(bootstrapExponent loss order - grade) = grade + -bootstrapExponent loss order by ring,
          Real.rpow_add positive]
        ring
  have series := tendstoUniformly_tsum_nat majorant paid
  simpa only [GuardedNewtonData.gradeLimit, GuardedNewtonData.grade_iterate_eq_sum] using series

end Grad.NashMoser.OriginalLimit
