import NewtonTimeProof

noncomputable section

namespace Grad.NashMoser.Numeric.Consumer

/-- The exact contract, with arbitrary real bootstrap powers. -/
theorem exact_time_and_tail : NewtonTimeGoal := newton_time_and_tail_sum

/-- Uniform downstream correction-tail estimate. The parameter set and
correction sequence are fixed before the grade and exponent are tested. -/
theorem correction_norm_tail {Parameter Value : Type*}
    [SeminormedAddCommGroup Value]
    (parameters : Set Parameter) (correction : Parameter → ℕ → Value)
    (initial grade exponent highConstant decayConstant : ℝ)
    (large : 4 ≤ initial) (highNonnegative : 0 ≤ highConstant)
    (decayNonnegative : 0 ≤ decayConstant) (gap : grade + 2 ≤ exponent)
    (correctionBound : ∀ parameter ∈ parameters, ∀ index : ℕ,
      ‖correction parameter index‖ ≤ highConstant * decayConstant *
        newtonTime initial index ^ (-(exponent - grade))) :
    ∀ parameter ∈ parameters, ∀ index : ℕ,
      Summable (fun offset : ℕ => ‖correction parameter (index + offset)‖) ∧
      (∑' offset : ℕ, ‖correction parameter (index + offset)‖) ≤
        2 * highConstant * decayConstant *
          newtonTime initial index ^ (-(exponent - grade)) := by
  intro parameter membership index
  have numericTail := newtonTime_tail large (by linarith : 2 ≤ exponent - grade) index
  have factorNonnegative : 0 ≤ highConstant * decayConstant :=
    mul_nonneg highNonnegative decayNonnegative
  have majorantSummable := numericTail.1.mul_left (highConstant * decayConstant)
  have normSummable : Summable (fun offset : ℕ =>
      ‖correction parameter (index + offset)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun _ => correctionBound parameter membership _) majorantSummable
  refine ⟨normSummable, ?_⟩
  calc
    _ ≤ ∑' offset : ℕ, highConstant * decayConstant *
        newtonTime initial (index + offset) ^ (-(exponent - grade)) :=
      Summable.tsum_le_tsum (fun _ => correctionBound parameter membership _)
        normSummable majorantSummable
    _ = highConstant * decayConstant *
        (∑' offset : ℕ, newtonTime initial (index + offset) ^
          (-(exponent - grade))) := tsum_mul_left
    _ ≤ highConstant * decayConstant *
        (2 * newtonTime initial index ^ (-(exponent - grade))) :=
      mul_le_mul_of_nonneg_left numericTail.2 factorNonnegative
    _ = _ := by ring

end Grad.NashMoser.Numeric.Consumer
