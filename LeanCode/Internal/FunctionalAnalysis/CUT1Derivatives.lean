import CUT1Cover

noncomputable section

open Grad.PDEBootstrap Grad.WeakTesting
open Grad.WeakTesting.Commutation (listDerivative listDerivative_ofFn listDerivative_perm)
open Grad.WeightedJets.SpatialMultiplier (scalarDerivative scalarDerivative_list scalarDerivative_smooth
  compactDerivative_bound)
open scoped ContDiff

namespace Grad.CompactCutoff

theorem list_counts (word : List (Fin 2)) : word.count 0 + word.count 1 = word.length := by
  induction word with
  | nil => simp
  | cons direction rest induction =>
    fin_cases direction <;> simp_all <;> omega

theorem list_canonical_perm (word : List (Fin 2)) :
    word.Perm (List.replicate (word.count 0) 0 ++ List.replicate (word.count 1) 1) := by
  apply List.perm_iff_count.mpr
  intro direction
  fin_cases direction <;> simp [List.count_replicate]

theorem wordIndex_degree (rank : ℕ) (word : Fin rank → Fin 2) :
    (wordIndex word).1 + (wordIndex word).2 = rank := by
  simpa only [wordIndex, List.length_ofFn] using list_counts (List.ofFn word)

theorem orderedDerivative_canonical (rank : ℕ) (word : Fin rank → Fin 2)
    (scalar : Spatial → ℝ) (smoothness : ContDiff ℝ ∞ scalar) :
    orderedTestDerivative rank word scalar = scalarDerivative (wordIndex word) scalar := by
  rw [← listDerivative_ofFn rank word scalar smoothness, scalarDerivative_list _ scalar smoothness]
  exact listDerivative_perm (list_canonical_perm (List.ofFn word)) scalar smoothness

theorem orderedDerivative_bound {compactSet domain : Set Spatial}
    (cutoff : Cutoff compactSet domain) (rank : ℕ) (word : Fin rank → Fin 2) (point : Spatial) :
    |orderedTestDerivative rank word cutoff.toFun point| ≤ orderedBound cutoff word := by
  rw [orderedDerivative_canonical rank word cutoff.toFun cutoff.smooth]
  exact (compactDerivative_bound (wordIndex word) cutoff.toFun cutoff.smooth cutoff.compact).choose_spec point

theorem ordered_derivative_consumer : OrderedDerivativeGoal := by
  intro compactSet domain cutoff
  constructor
  · intro rank word
    refine ⟨wordIndex_degree rank word, orderedDerivative_canonical rank word cutoff.toFun cutoff.smooth,
      ?_, orderedTestDerivative_hasCompactSupport rank word cutoff.toFun cutoff.compact,
      orderedTestDerivative_support_subset rank word cutoff.toFun, orderedDerivative_bound cutoff rank word⟩
    rw [orderedDerivative_canonical rank word cutoff.toFun cutoff.smooth]
    exact scalarDerivative_smooth (wordIndex word) cutoff.toFun cutoff.smooth
  · intro word
    refine ⟨orderedTestDerivative_zero word cutoff.toFun, fun point => ?_⟩
    change |cutoff.toFun point| ≤ 1
    rw [abs_of_nonneg (cutoff.nonnegative point)]
    exact cutoff.atMostOne point

end Grad.CompactCutoff
