import GuardedNewtonIteration
import Mathlib.Analysis.Normed.Group.InfiniteSum

noncomputable section

open Filter
open scoped BigOperators Topology

namespace Grad.NashMoser.Numeric.GuardedNewtonData

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [SeminormedAddCommGroup F] [NormedAddCommGroup G]
  {initial radius highConstant quadratic : ℝ} {smoothing : ℕ → ℝ} {loss : ℕ}
  (data : GuardedNewtonData E F initial radius highConstant quadratic smoothing loss)

/-- The grade image of the actual correction of the constructed sequence. -/
def gradeCorrection (gradeMap : E →+ G) (index : ℕ) : G :=
  gradeMap (data.correction index (data.admissibleState (data.stages index)))

theorem grade_iterate_eq_sum (gradeMap : E →+ G) (index : ℕ) :
    gradeMap (data.iterate index) =
      ∑ stage ∈ Finset.range index, data.gradeCorrection gradeMap stage := by
  induction index with
  | zero => simp only [data.iterate_zero, map_zero, Finset.range_zero, Finset.sum_empty]
  | succ index inductionHypothesis =>
    rw [data.iterate_step, map_add, inductionHypothesis, Finset.sum_range_succ]
    rfl

/-- All-grade numerical improvement is applied to this constructed sequence,
not to an assumed limiting solution. -/
theorem grade_correction_tail (gradeMap : E →+ G) (grade gradeConstant : ℝ)
    (gradeNonnegative : 0 ≤ gradeConstant)
    (gradeBound : ∀ index,
      ‖data.gradeCorrection gradeMap index‖ ≤ gradeConstant *
        newtonTime initial index ^ grade * ‖data.mapping (data.iterate index)‖) :
    ∃ order : ℕ, grade + 2 ≤ bootstrapExponent loss order ∧
      ∀ index : ℕ,
        Summable (fun offset : ℕ => ‖data.gradeCorrection gradeMap (index + offset)‖) ∧
        (∑' offset : ℕ, ‖data.gradeCorrection gradeMap (index + offset)‖) ≤
          2 * gradeConstant * bootstrapConstant initial loss quadratic smoothing order *
            newtonTime initial index ^ (-(bootstrapExponent loss order - grade)) := by
  obtain ⟨order, orderBound, tails⟩ := uniform_correction_tail_from_recurrence
    (Set.univ : Set Unit) initial loss quadratic smoothing
    (fun _ index => ‖data.mapping (data.iterate index)‖)
    (fun _ => data.gradeCorrection gradeMap)
    data.initialLarge (by exact_mod_cast data.lossLarge)
    data.quadraticNonnegative data.smoothingNonnegative
    (fun _ _ _ => norm_nonneg _) (fun _ _ => data.iterate_residual_decay)
    (fun _ _ => data.iterate_allCutoffRecurrence)
    grade gradeConstant gradeNonnegative (fun _ _ => gradeBound)
  exact ⟨order, orderBound, tails () (Set.mem_univ ())⟩

/-- Each complete grade receives the sum of the very same corrections. -/
def gradeLimit (gradeMap : E →+ G) : G :=
  ∑' index : ℕ, data.gradeCorrection gradeMap index

theorem grade_iterate_tendsto [CompleteSpace G]
    (gradeMap : E →+ G) (grade gradeConstant : ℝ)
    (gradeNonnegative : 0 ≤ gradeConstant)
    (gradeBound : ∀ index,
      ‖data.gradeCorrection gradeMap index‖ ≤ gradeConstant *
        newtonTime initial index ^ grade * ‖data.mapping (data.iterate index)‖) :
    Tendsto (fun index => gradeMap (data.iterate index)) atTop
      (𝓝 (data.gradeLimit gradeMap)) := by
  obtain ⟨_, _, tails⟩ := data.grade_correction_tail gradeMap grade gradeConstant
    gradeNonnegative gradeBound
  have normSummable : Summable (fun index => ‖data.gradeCorrection gradeMap index‖) := by
    simpa only [zero_add] using (tails 0).1
  have summable : Summable (data.gradeCorrection gradeMap) := normSummable.of_norm
  simpa only [data.grade_iterate_eq_sum, gradeLimit] using
    summable.hasSum.tendsto_sum_nat

/-- Limits in different completed grades agree under their actual continuous
inclusion map, by uniqueness of limits. -/
theorem gradeLimit_compatible
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ G] [NormedSpace ℝ H]
    (firstMap : E →+ G) (secondMap : E →+ H) (inclusion : G →L[ℝ] H)
    (commutes : ∀ state, inclusion (firstMap state) = secondMap state)
    (firstConverges : Tendsto (fun index => firstMap (data.iterate index)) atTop
      (𝓝 (data.gradeLimit firstMap)))
    (secondConverges : Tendsto (fun index => secondMap (data.iterate index)) atTop
      (𝓝 (data.gradeLimit secondMap))) :
    inclusion (data.gradeLimit firstMap) = data.gradeLimit secondMap := by
  have included := (inclusion.continuous.tendsto (data.gradeLimit firstMap)).comp
    firstConverges
  simp only [Function.comp_def, commutes] at included
  exact tendsto_nhds_unique included secondConverges

end Grad.NashMoser.Numeric.GuardedNewtonData
