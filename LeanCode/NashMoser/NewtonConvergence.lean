import NewtonBootstrap

noncomputable section

open Filter

namespace Grad.NashMoser.Numeric

/-- The same parameter set, residuals, corrections, constants and times work
at each requested grade. Selection of the bootstrap order is independent of
the parameter. This is the numerical implication used after constructing the
actual nonlinear recurrence. -/
theorem uniform_correction_tail_from_recurrence
    {Parameter Value : Type*} [SeminormedAddCommGroup Value]
    (parameters : Set Parameter)
    (initial loss quadratic : ℝ) (smoothing : ℕ → ℝ)
    (residual : Parameter → ℕ → ℝ) (correction : Parameter → ℕ → Value)
    (initialLarge : 4 ≤ initial) (lossLarge : 1 ≤ loss)
    (quadraticNonnegative : 0 ≤ quadratic)
    (smoothingNonnegative : ∀ cutoff, 0 ≤ smoothing cutoff)
    (residualNonnegative : ∀ parameter ∈ parameters, ∀ index, 0 ≤ residual parameter index)
    (baseDecay : ∀ parameter ∈ parameters, ∀ index,
      residual parameter index ≤ newtonTime initial index ^ (-initialDecay loss))
    (recurrence : ∀ parameter ∈ parameters, ∀ index cutoff,
      residual parameter (index + 1) ≤
        quadratic * newtonTime initial index ^ (2 * loss) * residual parameter index ^ 2 +
        smoothing cutoff * newtonTime initial index ^
          (-(((cutoff : ℝ) - 8 * loss) / 3)))
    (grade highConstant : ℝ) (highNonnegative : 0 ≤ highConstant)
    (correctionBound : ∀ parameter ∈ parameters, ∀ index,
      ‖correction parameter index‖ ≤ highConstant *
        newtonTime initial index ^ grade * residual parameter index) :
    ∃ order : ℕ, grade + 2 ≤ bootstrapExponent loss order ∧
      ∀ parameter ∈ parameters, ∀ index : ℕ,
        Summable (fun offset : ℕ => ‖correction parameter (index + offset)‖) ∧
        (∑' offset : ℕ, ‖correction parameter (index + offset)‖) ≤
          2 * highConstant * bootstrapConstant initial loss quadratic smoothing order *
            newtonTime initial index ^ (-(bootstrapExponent loss order - grade)) := by
  obtain ⟨order, orderBound⟩ :=
    ((tendsto_atTop.1 (bootstrapExponent_tendsto lossLarge)) (grade + 2)).exists
  refine ⟨order, orderBound, ?_⟩
  apply Consumer.correction_norm_tail parameters correction initial grade
    (bootstrapExponent loss order) highConstant
    (bootstrapConstant initial loss quadratic smoothing order)
    initialLarge highNonnegative
    (le_trans (by norm_num) (bootstrapConstant_one_le _ _ _ _ _)) orderBound
  intro parameter membership index
  have decay := same_sequence_bootstrap_decay initial loss quadratic smoothing
    (residual parameter) initialLarge lossLarge quadraticNonnegative
    smoothingNonnegative (residualNonnegative parameter membership)
    (baseDecay parameter membership) (recurrence parameter membership) order index
  have timePositive := newtonTime_pos (by linarith : 0 < initial) index
  calc
    _ ≤ highConstant * newtonTime initial index ^ grade * residual parameter index :=
      correctionBound parameter membership index
    _ ≤ highConstant * newtonTime initial index ^ grade *
        (bootstrapConstant initial loss quadratic smoothing order *
          newtonTime initial index ^ (-bootstrapExponent loss order)) :=
      mul_le_mul_of_nonneg_left decay
        (mul_nonneg highNonnegative (Real.rpow_nonneg timePositive.le _))
    _ = _ := by
      rw [show -(bootstrapExponent loss order - grade) =
        grade + -bootstrapExponent loss order by ring, Real.rpow_add timePositive]
      ring

end Grad.NashMoser.Numeric
