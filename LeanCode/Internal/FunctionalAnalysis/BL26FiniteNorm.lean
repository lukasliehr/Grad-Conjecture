import BL25FiniteBoundary

noncomputable section

open Set
open scoped BigOperators

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

def finiteNestedSupport {dimension : ℕ} (values : FiniteBoundaryData dimension) : Finset (ℤ × ℤ) :=
  values.support.biUnion (fun cell => (values cell).support.image (fun mode => (cell, mode)))

theorem finiteNestedSupport_missing {dimension : ℕ} (values : FiniteBoundaryData dimension)
    (cell mode : ℤ) (missing : (cell, mode) ∉ finiteNestedSupport values) : values cell mode = 0 := by
  classical
  by_contra nonzero
  apply missing
  rw [finiteNestedSupport, Finset.mem_biUnion]
  have cellNonzero : values cell ≠ 0 := by
    intro zeroCell
    exact nonzero (congrArg (fun row : ℤ →₀ ComplexEuclidean dimension => row mode) zeroCell)
  exact ⟨cell, Finsupp.mem_support_iff.mpr cellNonzero,
    Finset.mem_image.mpr ⟨mode, Finsupp.mem_support_iff.mpr nonzero, rfl⟩⟩

def finiteBoundaryEnergy {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (values : FiniteBoundaryData dimension) (cell mode : ℤ) : ℝ :=
  Real.exp (2 * boundaryPhase parameters cell) * boundaryFrequency (mode, cell) ^ (2 * grade - 1) *
    ‖values cell mode‖ ^ 2

theorem finiteBoundaryEnergy_summable {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (values : FiniteBoundaryData dimension) :
    Summable (fun pair : ℤ × ℤ => finiteBoundaryEnergy parameters grade values pair.1 pair.2) := by
  apply summable_of_ne_finset_zero (s := finiteNestedSupport values)
  intro pair missing
  rw [finiteBoundaryEnergy, finiteNestedSupport_missing values pair.1 pair.2 missing, norm_zero,
    zero_pow (by norm_num), mul_zero]

theorem finiteBoundaryToGrade_norm_sq {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (values : FiniteBoundaryData dimension) :
    ‖finiteBoundaryToGrade parameters grade gradePositive values‖ ^ 2 =
      ∑ cell ∈ values.support, ∑ mode ∈ (values cell).support,
        Real.exp (2 * boundaryPhase parameters cell) * boundaryFrequency (mode, cell) ^ (2 * grade - 1) *
          ‖values cell mode‖ ^ 2 := by
  rw [boundary_norm_sq]
  simp_rw [finiteBoundaryToGrade_coefficient]
  rw [← (Equiv.prodComm ℤ ℤ).tsum_eq (fun mode : ℤ × ℤ =>
    Real.exp (2 * boundaryPhase parameters mode.2) * boundaryFrequency mode ^ (2 * grade - 1) *
      ‖values mode.2 mode.1‖ ^ 2)]
  change (∑' pair : ℤ × ℤ, finiteBoundaryEnergy parameters grade values pair.1 pair.2) = _
  rw [(finiteBoundaryEnergy_summable parameters grade values).tsum_prod]
  rw [tsum_eq_sum (s := values.support) (fun cell missing => by
    have zeroRow : values cell = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using missing
    simp only [finiteBoundaryEnergy, zeroRow, Finsupp.zero_apply, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, tsum_zero])]
  apply Finset.sum_congr rfl
  intro cell _
  apply tsum_eq_sum
  intro mode missing
  have zeroValue : values cell mode = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using missing
  simp only [finiteBoundaryEnergy, zeroValue, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]

theorem finiteLiftLinear_relative_norm_sq {dimension : ℕ} (parameters : PhaseParameters)
    (values : FiniteBoundaryData dimension) (grade : ℕ) (gradePositive : 1 ≤ grade) :
    ‖GradeCore.ofCoreLinear (grade := grade) (finiteLiftLinear parameters dimension values)‖ ^ 2 ≤
      originalLiftCellConstant parameters grade * ‖finiteBoundaryToGrade parameters grade gradePositive values‖ ^ 2 := by
  rw [finiteBoundaryToGrade_norm_sq]
  exact finiteLiftLinear_original_bound parameters values grade gradePositive

theorem finiteLiftLinear_relative_norm {dimension : ℕ} (parameters : PhaseParameters)
    (values : FiniteBoundaryData dimension) (grade : ℕ) (gradePositive : 1 ≤ grade) :
    ‖GradeCore.ofCoreLinear (grade := grade) (finiteLiftLinear parameters dimension values)‖ ≤
      Real.sqrt (originalLiftCellConstant parameters grade) * ‖finiteBoundaryToGrade parameters grade gradePositive values‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (originalLiftCellConstant_nonnegative parameters grade)]
  exact finiteLiftLinear_relative_norm_sq parameters values grade gradePositive

end Grad.BoundaryLift
