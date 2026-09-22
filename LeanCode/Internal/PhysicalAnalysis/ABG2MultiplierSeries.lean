import ABG1OrdinaryAngularModes
import Mathlib.Analysis.PSeries

noncomputable section
open scoped BigOperators
namespace Grad.OrdinaryDiskMultiplier
open Grad.CircularHighWeak Grad.Constraints

def correctionCoefficient (mode : ℤ) : ℝ :=
  if mode ∈ lowAngularModes then 1 else 4 / (mode : ℝ) ^ 2

theorem correctionCoefficient_nonnegative (mode : ℤ) : 0 ≤ correctionCoefficient mode := by
  unfold correctionCoefficient
  split_ifs <;> positivity

theorem correctionCoefficient_literal (mode : ℤ) :
    1 - correctionCoefficient mode = highMultiplier mode := by
  by_cases low : mode ∈ lowAngularModes <;> simp [correctionCoefficient, highMultiplier, low]

theorem correctionCoefficient_summable : Summable correctionCoefficient := by
  have finite : Summable (fun mode : ℤ => if mode ∈ lowAngularModes then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := lowAngularModes) (fun mode outside => if_neg outside)
  have series : Summable (fun mode : ℤ => 4 / (mode : ℝ) ^ 2) := by
    simpa only [mul_one_div] using (Real.summable_one_div_int_pow.mpr (by decide : 1 < 2)).mul_left 4
  apply (finite.add series).of_nonneg_of_le correctionCoefficient_nonnegative
  intro mode
  by_cases low : mode ∈ lowAngularModes <;> simp only [correctionCoefficient, low, if_true, if_false]
  · exact le_add_of_nonneg_right (div_nonneg (by norm_num) (sq_nonneg _))
  · simp

/-- Absolute scalar correction mass; finite and independent of Sobolev grade. -/
def correctionMass : ℝ := ∑' mode : ℤ, correctionCoefficient mode

theorem correctionMass_nonnegative : 0 ≤ correctionMass := tsum_nonneg correctionCoefficient_nonnegative

section GenericSeries
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def correctedOperator (projections : ℤ → E →L[ℂ] E) : E →L[ℂ] E :=
  ContinuousLinearMap.id ℂ E - ∑' mode : ℤ, (correctionCoefficient mode : ℂ) • projections mode

omit [CompleteSpace E] in
theorem correctionOperator_norm_summable (projections : ℤ → E →L[ℂ] E)
    (constant : ℝ) (bound : ∀ mode, ‖projections mode‖ ≤ constant) :
    Summable (fun mode : ℤ => ‖(correctionCoefficient mode : ℂ) • projections mode‖) := by
  apply (correctionCoefficient_summable.mul_right constant).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro mode
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (correctionCoefficient_nonnegative mode)]
  exact mul_le_mul_of_nonneg_left (bound mode) (correctionCoefficient_nonnegative mode)

theorem correctedOperator_apply (projections : ℤ → E →L[ℂ] E)
    (constant : ℝ) (bound : ∀ mode, ‖projections mode‖ ≤ constant) (field : E) :
    correctedOperator projections field = field - ∑' mode : ℤ,
      (correctionCoefficient mode : ℂ) • projections mode field := by
  change field - (∑' mode : ℤ, (correctionCoefficient mode : ℂ) • projections mode) field = _
  congr 1
  exact (ContinuousLinearMap.apply ℂ E field).map_tsum
    (correctionOperator_norm_summable projections constant bound).of_norm

theorem correctionValue_summable (projections : ℤ → E →L[ℂ] E)
    (constant : ℝ) (bound : ∀ mode, ‖projections mode‖ ≤ constant) (field : E) :
    Summable (fun mode : ℤ => (correctionCoefficient mode : ℂ) • projections mode field) :=
  ((ContinuousLinearMap.apply ℂ E field).hasSum
    (correctionOperator_norm_summable projections constant bound).of_norm.hasSum).summable

omit [CompleteSpace E] in
theorem correctedOperator_bound (projections : ℤ → E →L[ℂ] E)
    (constant : ℝ) (bound : ∀ mode, ‖projections mode‖ ≤ constant) (field : E) :
    ‖correctedOperator projections field‖ ≤ (1 + correctionMass * constant) * ‖field‖ := by
  have operatorBound : ‖∑' mode : ℤ, (correctionCoefficient mode : ℂ) • projections mode‖ ≤
      correctionMass * constant := by
    refine (norm_tsum_le_tsum_norm (correctionOperator_norm_summable projections constant bound)).trans ?_
    have termBound (mode : ℤ) : ‖(correctionCoefficient mode : ℂ) • projections mode‖ ≤
        correctionCoefficient mode * constant := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (correctionCoefficient_nonnegative mode)]
      exact mul_le_mul_of_nonneg_left (bound mode) (correctionCoefficient_nonnegative mode)
    exact ((correctionOperator_norm_summable projections constant bound).tsum_le_tsum termBound
      (correctionCoefficient_summable.mul_right constant)).trans_eq (tsum_mul_right)
  change ‖field - (∑' mode : ℤ, (correctionCoefficient mode : ℂ) • projections mode) field‖ ≤ _
  have normBound := (ContinuousLinearMap.le_opNorm
    (∑' mode : ℤ, (correctionCoefficient mode : ℂ) • projections mode) field).trans
      (mul_le_mul_of_nonneg_right operatorBound (norm_nonneg field))
  calc
    _ ≤ ‖field‖ + ‖(∑' mode : ℤ, (correctionCoefficient mode : ℂ) • projections mode) field‖ := norm_sub_le _ _
    _ ≤ ‖field‖ + correctionMass * constant * ‖field‖ := add_le_add le_rfl normBound
    _ = (1 + correctionMass * constant) * ‖field‖ := by ring

theorem correctedOperator_natural {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (projections : ℤ → E →L[ℂ] E) (target : ℤ → F →L[ℂ] F)
    (constant targetConstant : ℝ) (bound : ∀ mode, ‖projections mode‖ ≤ constant)
    (targetBound : ∀ mode, ‖target mode‖ ≤ targetConstant) (mapping : E →L[ℂ] F)
    (commuting : ∀ mode field, mapping (projections mode field) = target mode (mapping field)) (field : E) :
    mapping (correctedOperator projections field) = correctedOperator target (mapping field) := by
  rw [correctedOperator_apply projections constant bound, correctedOperator_apply target targetConstant targetBound,
    map_sub, mapping.map_tsum (correctionValue_summable projections constant bound field)]
  congr 1
  apply tsum_congr
  intro mode
  rw [map_smul, commuting]

end GenericSeries
end Grad.OrdinaryDiskMultiplier
