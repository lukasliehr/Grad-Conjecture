import GC15Interface

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Allocation

open Grad.CartesianState Grad.NonlinearProduct Grad.FourierInterpolation

theorem physicalBudget_nonnegative (parameters : PhaseParameters) (field : ACore parameters 3)
    (rho epsilon : ℝ) (grade : ℕ) : 0 ≤ physicalBudget parameters field rho epsilon grade := by
  unfold physicalBudget
  exact add_nonneg (add_nonneg (originalGradeNorm_nonnegative _ _) (abs_nonneg _)) (abs_nonneg _)

theorem physicalBudget_monotone (parameters : PhaseParameters) (field : ACore parameters 3)
    (rho epsilon : ℝ) {low high : ℕ} (ordered : low ≤ high) :
    physicalBudget parameters field rho epsilon low ≤ physicalBudget parameters field rho epsilon high := by
  have bound := cartesianGrade_norm_mono (dimension := 3) parameters ordered field
  unfold physicalBudget originalGradeNorm
  linarith

def physicalInterpolationConstant (offset grade : ℕ) : ℝ :=
  1 + ∑ order : Fin (grade + 1),
    originalInterpolationConstant offset (offset + order.val) (offset + grade)

theorem physicalInterpolationConstant_one_le (offset grade : ℕ) :
    1 ≤ physicalInterpolationConstant offset grade := by
  exact le_add_of_nonneg_right (Finset.sum_nonneg
    (fun order _ => originalInterpolationConstant_nonnegative _ _ _))

theorem originalConstant_le_physical (offset grade order : ℕ) (orderLe : order ≤ grade) :
    originalInterpolationConstant offset (offset + order) (offset + grade) ≤
      physicalInterpolationConstant offset grade := by
  have single := Finset.single_le_sum
    (f := fun index : Fin (grade + 1) =>
      originalInterpolationConstant offset (offset + index.val) (offset + grade))
    (s := Finset.univ) (fun index _ => originalInterpolationConstant_nonnegative _ _ _)
    (Finset.mem_univ (⟨order, by omega⟩ : Fin (grade + 1)))
  exact single.trans (le_add_of_nonneg_left zero_le_one)

/-- Finite Hölder includes zero summands; no positive low norm is assumed. -/
theorem finite_interpolation_sum {Index : Type*} [Fintype Index]
    (low high : Index → ℝ) (lowNonnegative : ∀ index, 0 ≤ low index)
    (highNonnegative : ∀ index, 0 ≤ high index) {theta : ℝ}
    (thetaPositive : 0 < theta) (thetaLess : theta < 1) :
    (∑ index, low index ^ (1 - theta) * high index ^ theta) ≤
      (∑ index, low index) ^ (1 - theta) * (∑ index, high index) ^ theta := by
  have firstNonzero : 1 - theta ≠ 0 := (sub_pos.mpr thetaLess).ne'
  have lowPower (index : Index) :
      (low index ^ (1 - theta)) ^ (1 - theta)⁻¹ = low index := by
    rw [← Real.rpow_mul (lowNonnegative index), mul_inv_cancel₀ firstNonzero, Real.rpow_one]
  have highPower (index : Index) :
      (high index ^ theta) ^ theta⁻¹ = high index := by
    rw [← Real.rpow_mul (highNonnegative index), mul_inv_cancel₀ thetaPositive.ne', Real.rpow_one]
  have holder := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ)
    (f := fun index => low index ^ (1 - theta)) (g := fun index => high index ^ theta)
    (Real.HolderConjugate.one_sub_inv_inv thetaPositive thetaLess)
    (fun index _ => Real.rpow_nonneg (lowNonnegative index) _)
    (fun index _ => Real.rpow_nonneg (highNonnegative index) _)
  simpa only [lowPower, highPower, one_div, inv_inv] using holder

theorem nonnegative_interpolation_self {value theta : ℝ} (nonnegative : 0 ≤ value)
    (thetaPositive : 0 < theta) (thetaLess : theta < 1) :
    value ^ (1 - theta) * value ^ theta = value := by
  by_cases zero : value = 0
  · simp only [zero, Real.zero_rpow (sub_pos.mpr thetaLess).ne',
      Real.zero_rpow thetaPositive.ne', zero_mul]
  · rw [← Real.rpow_add (lt_of_le_of_ne nonnegative (Ne.symm zero)),
      sub_add_cancel, Real.rpow_one]

theorem physical_budget_interpolation (offset grade order : ℕ)
    (gradePositive : 0 < grade) (orderLe : order ≤ grade)
    (parameters : PhaseParameters) (field : ACore parameters 3) (rho epsilon : ℝ) :
    physicalBudget parameters field rho epsilon (offset + order) ≤
      physicalInterpolationConstant offset grade *
        (physicalBudget parameters field rho epsilon offset ^ (1 - (order : ℝ) / grade) *
          physicalBudget parameters field rho epsilon (offset + grade) ^ ((order : ℝ) / grade)) := by
  have constantOne := physicalInterpolationConstant_one_le offset grade
  have constantNonnegative := zero_le_one.trans constantOne
  by_cases orderZero : order = 0
  · subst order
    simp only [Nat.add_zero, Nat.cast_zero, zero_div, sub_zero, Real.rpow_one, Real.rpow_zero, mul_one]
    exact le_mul_of_one_le_left (physicalBudget_nonnegative _ _ _ _ _) constantOne
  by_cases orderTop : order = grade
  · subst order
    rw [div_self (by exact_mod_cast gradePositive.ne'), sub_self,
      Real.rpow_zero, Real.rpow_one, one_mul]
    exact le_mul_of_one_le_left (physicalBudget_nonnegative _ _ _ _ _) constantOne
  have strictLow : offset < offset + order := by omega
  have strictHigh : offset + order < offset + grade := by omega
  have thetaEquality : interpolationTheta offset (offset + order) (offset + grade) =
      (order : ℝ) / grade := by simp [interpolationTheta]
  have thetaPositive : 0 < (order : ℝ) / grade := by
    rw [← thetaEquality]
    exact interpolationTheta_pos strictLow strictHigh
  have thetaLess : (order : ℝ) / grade < 1 := by
    rw [← thetaEquality]
    exact interpolationTheta_lt_one strictLow strictHigh
  have fieldBound := original_grade_interpolation strictLow strictHigh field
  rw [thetaEquality] at fieldBound
  have fieldBound' := fieldBound.trans (mul_le_mul_of_nonneg_right
    (originalConstant_le_physical offset grade order orderLe)
    (mul_nonneg (Real.rpow_nonneg (originalGradeNorm_nonnegative _ _) _)
      (Real.rpow_nonneg (originalGradeNorm_nonnegative _ _) _)))
  let low : Fin 3 → ℝ := ![originalGradeNorm offset field, |rho|, |epsilon|]
  let high : Fin 3 → ℝ := ![originalGradeNorm (offset + grade) field, |rho|, |epsilon|]
  have lowNonnegative (index : Fin 3) : 0 ≤ low index := by
    fin_cases index <;> simp [low, originalGradeNorm_nonnegative]
  have highNonnegative (index : Fin 3) : 0 ≤ high index := by
    fin_cases index <;> simp [high, originalGradeNorm_nonnegative]
  have finite := finite_interpolation_sum low high lowNonnegative highNonnegative thetaPositive thetaLess
  have rhoIdentity := nonnegative_interpolation_self (abs_nonneg rho) thetaPositive thetaLess
  have epsilonIdentity := nonnegative_interpolation_self (abs_nonneg epsilon) thetaPositive thetaLess
  have holder : originalGradeNorm offset field ^ (1 - (order : ℝ) / grade) *
      originalGradeNorm (offset + grade) field ^ ((order : ℝ) / grade) + |rho| + |epsilon| ≤
      physicalBudget parameters field rho epsilon offset ^ (1 - (order : ℝ) / grade) *
        physicalBudget parameters field rho epsilon (offset + grade) ^ ((order : ℝ) / grade) := by
    simpa [low, high, Fin.sum_univ_succ, rhoIdentity, epsilonIdentity, physicalBudget, add_assoc] using finite
  have rhoBound := le_mul_of_one_le_left (abs_nonneg rho) constantOne
  have epsilonBound := le_mul_of_one_le_left (abs_nonneg epsilon) constantOne
  calc
    physicalBudget parameters field rho epsilon (offset + order) ≤
        physicalInterpolationConstant offset grade *
          (originalGradeNorm offset field ^ (1 - (order : ℝ) / grade) *
            originalGradeNorm (offset + grade) field ^ ((order : ℝ) / grade) + |rho| + |epsilon|) := by
      unfold physicalBudget
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left holder constantNonnegative

theorem physicalInterpolationGoal : PhysicalInterpolationGoal := by
  intro offset grade positive
  refine ⟨physicalInterpolationConstant offset grade,
    zero_le_one.trans (physicalInterpolationConstant_one_le offset grade), ?_⟩
  intro parameters field rho epsilon order orderLe
  exact physical_budget_interpolation offset grade order positive orderLe parameters field rho epsilon

end Grad.GaugeCoefficients.Physical.Allocation
