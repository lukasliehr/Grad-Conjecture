import BL3RadialWeight

noncomputable section

open Set
open scoped BigOperators ContDiff

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace

theorem norm_iteratedDeriv_product_le (first second : ℝ → ℝ)
    (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second)
    (order : ℕ) (point : ℝ) :
    ‖iteratedDeriv order (fun source => first source * second source) point‖ ≤
      ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) *
        ‖iteratedDeriv index first point‖ * ‖iteratedDeriv (order - index) second point‖ := by
  have product := norm_iteratedFDerivWithin_smul_le (𝕜 := ℝ) (N := ∞) (n := order)
    (s := univ) firstSmooth.contDiffOn secondSmooth.contDiffOn uniqueDiffOn_univ
    (mem_univ point) (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  simpa only [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv, smul_eq_mul] using product

theorem exists_cutoffDerivative_bound (order : ℕ) : ∃ bound : ℝ, 0 ≤ bound ∧
    ∀ time ∈ Icc (0 : ℝ) (1 / 4), ‖iteratedDeriv order collarCutoff1D time‖ ≤ bound := by
  have smooth : Continuous (fun time => ‖iteratedDeriv order collarCutoff1D time‖) := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using
      (collarCutoff1D_smooth.continuous_iteratedFDeriv
        (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).norm
  obtain ⟨bound, bound_all⟩ := bddAbove_def.mp
    ((isCompact_Icc : IsCompact (Icc (0 : ℝ) (1 / 4))).bddAbove_image smooth.continuousOn)
  refine ⟨max bound 0, le_max_right _ _, ?_⟩
  intro time inside
  exact (bound_all _ ⟨time, inside, rfl⟩).trans (le_max_left _ _)

def cutoffDerivativeBound (order : ℕ) : ℝ := Classical.choose (exists_cutoffDerivative_bound order)

theorem cutoffDerivativeBound_nonnegative (order : ℕ) : 0 ≤ cutoffDerivativeBound order :=
  (Classical.choose_spec (exists_cutoffDerivative_bound order)).1

theorem cutoffDerivative_le (order : ℕ) (time : ℝ) (inside : time ∈ Icc (0 : ℝ) (1 / 4)) :
    ‖iteratedDeriv order collarCutoff1D time‖ ≤ cutoffDerivativeBound order :=
  (Classical.choose_spec (exists_cutoffDerivative_bound order)).2 time inside

theorem exponentialProfile_iterated_norm (mode : ℤ × ℤ) (order : ℕ) (time : ℝ) :
    ‖iteratedDeriv order (fun source : ℝ => Real.exp (-boundaryFrequency mode * source)) time‖ =
      boundaryFrequency mode ^ order * Real.exp (-boundaryFrequency mode * time) := by
  rw [iteratedDeriv_exp_const_mul, norm_mul, norm_pow, norm_neg,
    Real.norm_of_nonneg (boundaryFrequency_pos mode).le, Real.norm_of_nonneg (Real.exp_pos _).le]

def cutoffExponentialProfile (mode : ℤ × ℤ) (time : ℝ) : ℝ :=
  collarCutoff1D time * Real.exp (-boundaryFrequency mode * time)

theorem cutoffExponentialProfile_smooth (mode : ℤ × ℤ) :
    ContDiff ℝ ∞ (cutoffExponentialProfile mode) :=
  collarCutoff1D_smooth.mul ((contDiff_const.mul contDiff_id).exp)

def cutoffExponentialConstant (order : ℕ) : ℝ :=
  ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) * cutoffDerivativeBound index

theorem cutoffExponentialConstant_nonnegative (order : ℕ) : 0 ≤ cutoffExponentialConstant order :=
  Finset.sum_nonneg (fun index _ => mul_nonneg (Nat.cast_nonneg _) (cutoffDerivativeBound_nonnegative index))

theorem cutoffExponentialProfile_iterated_bound (mode : ℤ × ℤ) (order : ℕ) (time : ℝ)
    (inside : time ∈ Icc (0 : ℝ) (1 / 4)) :
    ‖iteratedDeriv order (cutoffExponentialProfile mode) time‖ ≤
      cutoffExponentialConstant order * boundaryFrequency mode ^ order *
        Real.exp (-boundaryFrequency mode * time) := by
  have product := norm_iteratedDeriv_product_le collarCutoff1D
    (fun source : ℝ => Real.exp (-boundaryFrequency mode * source)) collarCutoff1D_smooth
    ((contDiff_const.mul contDiff_id).exp) order time
  apply product.trans
  simp only [cutoffExponentialConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro index _
  rw [exponentialProfile_iterated_norm]
  have cutBound := cutoffDerivative_le index time inside
  have powerBound := pow_le_pow_right₀ (boundaryFrequency_one_le mode) (Nat.sub_le order index)
  have comparison := mul_le_mul
    (mul_le_mul_of_nonneg_left cutBound (Nat.cast_nonneg (order.choose index)))
    (mul_le_mul_of_nonneg_right powerBound (Real.exp_pos (-boundaryFrequency mode * time)).le)
    (mul_nonneg (pow_nonneg (boundaryFrequency_pos _).le _)
      (Real.exp_pos (-boundaryFrequency mode * time)).le)
    (mul_nonneg (Nat.cast_nonneg _) (cutoffDerivativeBound_nonnegative _))
  simpa only [mul_assoc] using comparison

end Grad.BoundaryLift
