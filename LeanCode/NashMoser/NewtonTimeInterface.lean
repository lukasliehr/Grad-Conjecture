import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section

namespace Grad.NashMoser.Numeric

/-- The single time scale chosen before any Newton or bootstrap index. -/
def newtonTime (initial : ℝ) (index : ℕ) : ℝ :=
  initial ^ ((3 / 2 : ℝ) ^ index)

/-- The numerical predecessor used at stage zero; it is not an iterate. -/
def predecessorTime (initial : ℝ) : ℝ := initial ^ (2 / 3 : ℝ)

/-- Exact real-exponent NM05/CAL41 contract. The tail is indexed by its
offset from the arbitrary starting index. -/
def NewtonTimeGoal : Prop :=
  ∀ initial : ℝ, 4 ≤ initial →
    (∀ index offset : ℕ,
      newtonTime initial index ^ (1 + (offset : ℝ) / 2) ≤
        newtonTime initial (index + offset)) ∧
    (∀ (index : ℕ) (exponent : ℝ), 2 ≤ exponent →
      Summable (fun offset : ℕ =>
        newtonTime initial (index + offset) ^ (-exponent)) ∧
      (∑' offset : ℕ, newtonTime initial (index + offset) ^ (-exponent)) ≤
        2 * newtonTime initial index ^ (-exponent))

end Grad.NashMoser.Numeric
