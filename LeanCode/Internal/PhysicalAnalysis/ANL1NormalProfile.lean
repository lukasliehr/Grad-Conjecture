import ARC10FiniteCartesianConsumer
import ABF2SameBulkSmoothRealization

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Grad.CircularNormalLift
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.BoundaryLift

/-- The literal inward-time normal lifting profile. -/
def normalProfile (mode : ℤ) (time : ℝ) : ℝ :=
  -time * cutoffExponentialProfile (mode, 0) time

theorem normalProfile_smooth (mode : ℤ) : ContDiff ℝ ∞ (normalProfile mode) :=
  contDiff_id.neg.mul (cutoffExponentialProfile_smooth _)

theorem iteratedDeriv_time_mul (profile : ℝ → ℝ) (smooth : ContDiff ℝ ∞ profile)
    (order : ℕ) (time : ℝ) :
    iteratedDeriv order (fun source => source * profile source) time =
      time * iteratedDeriv order profile time +
        (order : ℝ) * iteratedDeriv (order - 1) profile time := by
  have idSmooth : ContDiff ℝ order (fun source : ℝ => source) := contDiff_id
  rw [iteratedDeriv_fun_mul (f := fun source : ℝ => source) (g := profile) (n := order) (x := time) idSmooth.contDiffAt
    ((contDiff_infty.mp smooth) order).contDiffAt]
  simp_rw [iteratedDeriv_fun_id, mul_ite, ite_mul]
  cases order with
  | zero => simp
  | succ order =>
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp [Nat.choose_one_right]
    ring

theorem exists_halfCutoff_bound (order : ℕ) : ∃ bound : ℝ, 0 ≤ bound ∧
    ∀ time ∈ Icc (0 : ℝ) (1 / 2), ‖iteratedDeriv order collarCutoff1D time‖ ≤ bound := by
  have smooth : Continuous (fun time => ‖iteratedDeriv order collarCutoff1D time‖) := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using
      (collarCutoff1D_smooth.continuous_iteratedFDeriv
        (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).norm
  obtain ⟨bound, bound_all⟩ := bddAbove_def.mp
    ((isCompact_Icc : IsCompact (Icc (0 : ℝ) (1 / 2))).bddAbove_image smooth.continuousOn)
  refine ⟨max bound 0, le_max_right _ _, ?_⟩
  intro time inside
  exact (bound_all _ ⟨time, inside, rfl⟩).trans (le_max_left _ _)

def halfCutoffBound (order : ℕ) : ℝ := Classical.choose (exists_halfCutoff_bound order)

theorem halfCutoffBound_nonnegative (order : ℕ) : 0 ≤ halfCutoffBound order :=
  (Classical.choose_spec (exists_halfCutoff_bound order)).1

theorem halfCutoff_bound (order : ℕ) (time : ℝ) (inside : time ∈ Icc (0 : ℝ) (1 / 2)) :
    ‖iteratedDeriv order collarCutoff1D time‖ ≤ halfCutoffBound order :=
  (Classical.choose_spec (exists_halfCutoff_bound order)).2 time inside

def halfProfileConstant (order : ℕ) : ℝ :=
  ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) * halfCutoffBound index

theorem halfProfileConstant_nonnegative (order : ℕ) : 0 ≤ halfProfileConstant order :=
  Finset.sum_nonneg (fun index _ => mul_nonneg (Nat.cast_nonneg _) (halfCutoffBound_nonnegative index))

theorem halfProfile_bound (mode : ℤ) (order : ℕ) (time : ℝ)
    (inside : time ∈ Icc (0 : ℝ) (1 / 2)) :
    ‖iteratedDeriv order (cutoffExponentialProfile (mode, 0)) time‖ ≤
      halfProfileConstant order * boundaryFrequency (mode, 0) ^ order *
        Real.exp (-boundaryFrequency (mode, 0) * time) := by
  have product := norm_iteratedDeriv_product_le collarCutoff1D
    (fun source : ℝ => Real.exp (-boundaryFrequency (mode, 0) * source)) collarCutoff1D_smooth
    ((contDiff_const.mul contDiff_id).exp) order time
  apply product.trans
  simp only [halfProfileConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro index _
  rw [exponentialProfile_iterated_norm]
  have cutBound := halfCutoff_bound index time inside
  have powerBound := pow_le_pow_right₀ (boundaryFrequency_one_le (mode, 0)) (Nat.sub_le order index)
  have comparison := mul_le_mul
    (mul_le_mul_of_nonneg_left cutBound (Nat.cast_nonneg (order.choose index)))
    (mul_le_mul_of_nonneg_right powerBound (Real.exp_pos (-boundaryFrequency (mode, 0) * time)).le)
    (mul_nonneg (pow_nonneg (boundaryFrequency_pos _).le _) (Real.exp_pos (-boundaryFrequency (mode, 0) * time)).le)
    (mul_nonneg (Nat.cast_nonneg _) (halfCutoffBound_nonnegative _))
  simpa only [mul_assoc] using comparison

def normalProfileConstant (order : ℕ) : ℝ :=
  halfProfileConstant order + (order : ℝ) * halfProfileConstant (order - 1)

theorem normalProfileConstant_nonnegative (order : ℕ) : 0 ≤ normalProfileConstant order :=
  add_nonneg (halfProfileConstant_nonnegative _)
    (mul_nonneg (Nat.cast_nonneg _) (halfProfileConstant_nonnegative _))

theorem normalProfile_bound (mode : ℤ) (order : ℕ) (time : ℝ)
    (inside : time ∈ Icc (0 : ℝ) (1 / 2)) :
    ‖iteratedDeriv order (normalProfile mode) time‖ ≤
      normalProfileConstant order * boundaryFrequency (mode, 0) ^ order *
        ((boundaryFrequency (mode, 0))⁻¹ + time) * Real.exp (-boundaryFrequency (mode, 0) * time) := by
  let frequency := boundaryFrequency (mode, 0)
  have frequencyPositive : 0 < frequency := boundaryFrequency_pos _
  have expression : normalProfile mode = fun source => -(source * cutoffExponentialProfile (mode, 0) source) := by
    funext source
    simp only [normalProfile, neg_mul]
  rw [expression, iteratedDeriv_fun_neg, norm_neg, iteratedDeriv_time_mul _ (cutoffExponentialProfile_smooth _)]
  have bound := norm_add_le (time * iteratedDeriv order (cutoffExponentialProfile (mode, 0)) time)
    ((order : ℝ) * iteratedDeriv (order - 1) (cutoffExponentialProfile (mode, 0)) time)
  rw [norm_mul, norm_mul, Real.norm_of_nonneg inside.1, Real.norm_natCast] at bound
  have first := halfProfile_bound mode order time inside
  have second := halfProfile_bound mode (order - 1) time inside
  have estimate := bound.trans (add_le_add (mul_le_mul_of_nonneg_left first inside.1)
    (mul_le_mul_of_nonneg_left second (Nat.cast_nonneg order)))
  apply estimate.trans
  change time * (halfProfileConstant order * frequency ^ order * Real.exp (-frequency * time)) +
      (order : ℝ) * (halfProfileConstant (order - 1) * frequency ^ (order - 1) * Real.exp (-frequency * time)) ≤
    normalProfileConstant order * frequency ^ order * (frequency⁻¹ + time) * Real.exp (-frequency * time)
  cases order with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, add_zero, pow_zero, mul_one, normalProfileConstant]
    have nonnegative := mul_nonneg (halfProfileConstant_nonnegative 0) (inv_nonneg.mpr frequencyPositive.le)
    have exponentialPositive := Real.exp_pos (-frequency * time)
    nlinarith
  | succ order =>
    have power : frequency ^ order = frequency ^ (order + 1) * frequency⁻¹ := by
      rw [pow_succ]
      field_simp
    simp only [Nat.add_sub_cancel, normalProfileConstant]
    rw [power]
    have firstNonnegative := halfProfileConstant_nonnegative (order + 1)
    have secondNonnegative := halfProfileConstant_nonnegative order
    have extraFirst := mul_nonneg firstNonnegative (inv_nonneg.mpr frequencyPositive.le)
    have extraSecond := mul_nonneg
      (mul_nonneg (Nat.cast_nonneg (order + 1)) secondNonnegative) inside.1
    have positiveFactor := mul_pos (pow_pos frequencyPositive (order + 1)) (Real.exp_pos (-frequency * time))
    nlinarith

end Grad.CircularNormalLift
