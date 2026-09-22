import ACE8PositiveKernelBounds

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterVolterra
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct

local instance : CompactSpace ClosedDisk := by
  rw [← isCompact_iff_compactSpace, closedUnitDisk_eq_closedBall]
  exact isCompact_closedBall (0 : SpatialPlane) 1

def radiusOperatorDerivative (order : ℕ) : C(ClosedDisk, SpatialPlane [×order]→L[ℝ] ℝ) where
  toFun point := iteratedFDeriv ℝ order radiusSquare point.val
  continuous_toFun := (radiusSquare_smooth.continuous_iteratedFDeriv
    (by exact_mod_cast le_top)).comp continuous_subtype_val

def radiusDerivativeEnvelope (grade : ℕ) : ℝ :=
  1 + ∑ order ∈ Finset.range (grade + 1), ‖radiusOperatorDerivative order‖

def leibnizEnvelope (grade : ℕ) : ℝ :=
  1 + ∑ order ∈ Finset.range (grade + 1),
    ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ)

theorem radiusDerivativeEnvelope_one_le (grade : ℕ) : 1 ≤ radiusDerivativeEnvelope grade := by
  unfold radiusDerivativeEnvelope
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun order _ => norm_nonneg (radiusOperatorDerivative order)))

theorem leibnizEnvelope_one_le (grade : ℕ) : 1 ≤ leibnizEnvelope grade := by
  unfold leibnizEnvelope
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)))

theorem radiusDerivativeEnvelope_bound (grade order : ℕ) (upper : order ≤ grade) (point : ClosedDisk) :
    ‖iteratedFDeriv ℝ order radiusSquare point.val‖ ≤ radiusDerivativeEnvelope grade := by
  apply (ContinuousMap.norm_coe_le_norm (radiusOperatorDerivative order) point).trans
  have one := Finset.single_le_sum (f := fun order => ‖radiusOperatorDerivative order‖)
    (fun order _ => norm_nonneg (radiusOperatorDerivative order)) (Finset.mem_range.mpr (by omega : order < grade + 1))
  unfold radiusDerivativeEnvelope
  linarith

theorem leibnizEnvelope_bound (grade order : ℕ) (upper : order ≤ grade) :
    (∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ)) ≤ leibnizEnvelope grade := by
  have one := Finset.single_le_sum
    (f := fun order => ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ))
    (fun _ _ => Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
    (Finset.mem_range.mpr (by omega : order < grade + 1))
  unfold leibnizEnvelope
  linarith

def radiusIterationConstant (grade : ℕ) : ℝ := leibnizEnvelope grade * radiusDerivativeEnvelope grade

theorem radiusIterationConstant_one_le (grade : ℕ) : 1 ≤ radiusIterationConstant grade := by
  have first := leibnizEnvelope_one_le grade
  have second := radiusDerivativeEnvelope_one_le grade
  unfold radiusIterationConstant
  nlinarith

/-- A fixed-grade exponential polynomial bound suffices for the factorial
Volterra series. No radial extension or loss of source derivatives occurs. -/
theorem radiusPower_operator_bound (grade power order : ℕ) (upper : order ≤ grade) (point : ClosedDisk) :
    ‖iteratedFDeriv ℝ order (fun point => radiusSquare point ^ power) point.val‖ ≤
      radiusIterationConstant grade ^ power := by
  induction power generalizing order with
  | zero =>
    simp only [pow_zero]
    by_cases orderZero : order = 0
    · subst order
      simp
    · rw [iteratedFDeriv_const_of_ne orderZero]
      simp
  | succ power inductionHypothesis =>
    have radiusNonnegative : 0 ≤ radiusDerivativeEnvelope grade :=
      (by norm_num : (0 : ℝ) ≤ 1).trans (radiusDerivativeEnvelope_one_le grade)
    have constantNonnegative : 0 ≤ radiusIterationConstant grade :=
      (by norm_num : (0 : ℝ) ≤ 1).trans (radiusIterationConstant_one_le grade)
    have product := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := ∞) (n := order)
      (radiusSquare_smooth.pow power) radiusSquare_smooth point.val
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
    simp only [pow_succ]
    apply product.trans
    calc
      _ ≤ ∑ index ∈ Finset.range (order + 1),
          (order.choose index : ℝ) * radiusIterationConstant grade ^ power * radiusDerivativeEnvelope grade := by
        apply Finset.sum_le_sum
        intro index inside
        have indexUpper : index ≤ grade := by have := Finset.mem_range.mp inside; omega
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (inductionHypothesis index indexUpper) (Nat.cast_nonneg _))
          (radiusDerivativeEnvelope_bound grade (order - index) ((Nat.sub_le _ _).trans upper) point)
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg constantNonnegative _))
      _ = (∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ)) *
          radiusIterationConstant grade ^ power * radiusDerivativeEnvelope grade := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
      _ ≤ leibnizEnvelope grade * radiusIterationConstant grade ^ power * radiusDerivativeEnvelope grade :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (leibnizEnvelope_bound grade order upper)
          (pow_nonneg constantNonnegative _)) radiusNonnegative
      _ = radiusIterationConstant grade ^ power * radiusIterationConstant grade := by
        unfold radiusIterationConstant
        ring

end Grad.ActualCenterVolterra
