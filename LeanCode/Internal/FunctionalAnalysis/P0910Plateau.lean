import P0910Interface
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section

open Set
open scoped ContDiff Topology

namespace Grad.DiskExtension.Operator

theorem collar_constants :
    collarWidth = (1 / 4 : ℝ) ∧
    cutoffPlateauWidth = (1 / 12 : ℝ) ∧
    cutoffSupportWidth = (1 / 6 : ℝ) ∧
    innerCollarRadius = (3 / 4 : ℝ) ∧
    outerSupportRadius = (7 / 6 : ℝ) := by
  norm_num [collarWidth, cutoffPlateauWidth, cutoffSupportWidth,
    innerCollarRadius, outerSupportRadius]

theorem plateauCutoff_smooth : ContDiff ℝ ∞ plateauCutoff := by
  unfold plateauCutoff
  fun_prop

theorem plateauCutoff_range (scale : ℝ) :
    0 ≤ plateauCutoff scale ∧ plateauCutoff scale ≤ 1 := by
  constructor
  · unfold plateauCutoff
    linarith [Real.smoothTransition.le_one (12 * scale - 1)]
  · unfold plateauCutoff
    linarith [Real.smoothTransition.nonneg (12 * scale - 1)]

theorem plateauCutoff_one (scale : ℝ) (bound : scale ≤ cutoffPlateauWidth) :
    plateauCutoff scale = 1 := by
  rw [collar_constants.2.1] at bound
  unfold plateauCutoff
  rw [Real.smoothTransition.zero_of_nonpos]
  · ring
  · linarith

theorem plateauCutoff_zero (scale : ℝ) (bound : cutoffSupportWidth ≤ scale) :
    plateauCutoff scale = 0 := by
  rw [collar_constants.2.2.1] at bound
  unfold plateauCutoff
  rw [Real.smoothTransition.one_of_one_le]
  · ring
  · linarith

theorem plateauCutoff_iteratedDeriv_zero_left (order : ℕ) (positive : 0 < order)
    (scale : ℝ) (bound : scale < cutoffPlateauWidth) :
    iteratedDeriv order plateauCutoff scale = 0 := by
  have equality : Set.EqOn plateauCutoff (fun _ : ℝ => 1) (Set.Iio cutoffPlateauWidth) := by
    intro point membership
    exact plateauCutoff_one point membership.le
  rw [equality.iteratedDeriv_of_isOpen isOpen_Iio order bound]
  simp [iteratedDeriv_const, positive.ne']

theorem plateauCutoff_iteratedDeriv_zero_right (order : ℕ) (_positive : 0 < order)
    (scale : ℝ) (bound : cutoffSupportWidth < scale) :
    iteratedDeriv order plateauCutoff scale = 0 := by
  have equality : Set.EqOn plateauCutoff (fun _ : ℝ => 0) (Set.Ioi cutoffSupportWidth) := by
    intro point membership
    exact plateauCutoff_zero point membership.le
  rw [equality.iteratedDeriv_of_isOpen isOpen_Ioi order bound]
  simp

theorem plateauCutoff_iteratedDeriv_flat (order : ℕ) (positive : 0 < order) :
    iteratedDeriv order plateauCutoff 0 = 0 := by
  apply plateauCutoff_iteratedDeriv_zero_left order positive
  rw [collar_constants.2.1]
  norm_num

theorem plateauCutoff_iteratedDeriv_compact (order : ℕ) (positive : 0 < order) :
    HasCompactSupport (iteratedDeriv order plateauCutoff) := by
  rw [HasCompactSupport]
  apply (isCompact_Icc : IsCompact (Set.Icc cutoffPlateauWidth cutoffSupportWidth)).of_isClosed_subset
    isClosed_closure
  apply closure_minimal
  · intro scale nonzero
    by_contra outside
    simp only [mem_Icc, not_and_or, not_le] at outside
    rcases outside with left | right
    · exact nonzero (plateauCutoff_iteratedDeriv_zero_left order positive scale left)
    · exact nonzero (plateauCutoff_iteratedDeriv_zero_right order positive scale right)
  · exact isClosed_Icc

theorem plateauCutoff_iteratedDeriv_bound (order : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ scale,
      ‖iteratedDeriv order plateauCutoff scale‖ ≤ bound := by
  by_cases zero_order : order = 0
  · subst order
    refine ⟨1, zero_le_one, ?_⟩
    intro scale
    rw [iteratedDeriv_zero, Real.norm_eq_abs, abs_of_nonneg (plateauCutoff_range scale).1]
    exact (plateauCutoff_range scale).2
  · have positive : 0 < order := Nat.pos_of_ne_zero zero_order
    have continuousDerivative : Continuous (iteratedDeriv order plateauCutoff) :=
      (plateauCutoff_smooth.of_le
        (WithTop.coe_le_coe.mpr (show (order : ℕ∞) ≤ ⊤ from le_top))).continuous_iteratedDeriv order
        (by exact_mod_cast le_rfl)
    obtain ⟨bound, bound_all⟩ := continuousDerivative.bounded_above_of_compact_support
      (plateauCutoff_iteratedDeriv_compact order positive)
    refine ⟨max bound 0, le_max_right _ _, fun scale => ?_⟩
    exact (bound_all scale).trans (le_max_left _ _)

theorem plateau_goal : PlateauGoal :=
  ⟨plateauCutoff_smooth, plateauCutoff_range, plateauCutoff_one,
    plateauCutoff_zero, plateauCutoff_iteratedDeriv_flat,
    plateauCutoff_iteratedDeriv_bound⟩

end Grad.DiskExtension.Operator
