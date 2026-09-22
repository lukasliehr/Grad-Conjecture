import AXJ1RealAxisMaps

noncomputable section
namespace Grad.ChartAxisProjections
open Grad.ClosedJets Grad.CartesianState Grad.Constraints

theorem acore_real_sub {parameters : PhaseParameters} {dimension : ℕ}
    (first second : ACore parameters dimension) : first + (-1 : ℝ) • second = first - second := by
  apply Subtype.ext
  funext cell
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change ((first.val cell) + ((-1 : ℝ) : ℂ) • (second.val cell)).value point =
    ((first.val cell) - (second.val cell)).value point
  rw [Complex.ofReal_neg, Complex.ofReal_one, neg_one_smul, sub_eq_add_neg]

theorem stateCore_real_sub {parameters : PhaseParameters}
    (first second : Grad.SmoothingFamily.StateCore parameters) :
    first + (-1 : ℝ) • second = first - second := by
  apply Prod.ext
  · apply Subtype.ext
    funext cell
    change first.1.val cell + (-1 : ℝ) • second.1.val cell = first.1.val cell - second.1.val cell
    rw [neg_one_smul, sub_eq_add_neg]
  · exact Prod.ext (acore_real_sub first.2.1 second.2.1) (acore_real_sub first.2.2 second.2.2)

theorem sourceCore_real_sub {parameters : PhaseParameters}
    (first second : Grad.NonlinearQuotientBounds.QuotientRows parameters) :
    first + (-1 : ℝ) • second = first - second := by
  funext row
  exact acore_real_sub (first row) (second row)

theorem sourceRange_real_sub {parameters : PhaseParameters}
    (first second : Grad.RealFixedRanges.sourceSmoothRange parameters) :
    first + (-1 : ℝ) • second = first - second := by
  apply Subtype.ext
  exact sourceCore_real_sub (parameters := parameters) first.val second.val

end Grad.ChartAxisProjections
