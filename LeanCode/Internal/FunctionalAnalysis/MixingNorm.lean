import MixingInterface

open scoped BigOperators

namespace Grad.HilbertMixing

variable {Index : Type*} [Fintype Index] [DecidableEq Index]
variable {Value : Type*} [NormedAddCommGroup Value] [InnerProductSpace ℝ Value]

theorem norm_sq (coefficients : Index → Index → ℝ)
    (orthogonality : ∀ first second, ∑ output, coefficients first output * coefficients second output =
      if first = second then 1 else 0)
    (field : PiLp 2 (fun _ : Index => Value)) : ‖mix coefficients field‖ ^ 2 = ‖field‖ ^ 2 := by
  calc
    ‖mix coefficients field‖ ^ 2 =
        ∑ output, inner ℝ (∑ first, coefficients first output • field first)
          (∑ second, coefficients second output • field second) := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp only [real_inner_self_eq_norm_sq]
      rfl
    _ = ∑ output, ∑ first, ∑ second,
        (coefficients first output * coefficients second output) *
          inner ℝ (field second) (field first) := by
      simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
        mul_assoc]
    _ = ∑ first, ∑ second, (∑ output, coefficients first output * coefficients second output) *
        inner ℝ (field second) (field first) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro first membership
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = ∑ first, ‖field first‖ ^ 2 := by
      simp [orthogonality, ite_mul]
    _ = ‖field‖ ^ 2 := (PiLp.norm_sq_eq_of_L2 _ field).symm

end Grad.HilbertMixing
