import SBT1BoundaryWeights

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.SourceBoundaryTrace
open Grad.SourceCollarDivision Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace

def integerBoundaryEmbedding {dimension grade power : ℕ} (paid : power + 1 ≤ grade) :
    SourceBoundary dimension →L[ℂ] SourceBoundary dimension :=
  sequenceMultiplier (fun mode => (integerBoundaryRatio grade power mode : ℂ))
    ((3 : ℝ) ^ power) (by positivity) (fun mode => by
      rw [Complex.norm_real, Real.norm_of_nonneg (integerBoundaryRatio_nonnegative grade power mode)]
      exact integerBoundaryRatio_bound paid mode)

theorem integerBoundaryEmbedding_bound {dimension grade power : ℕ} (paid : power + 1 ≤ grade)
    (field : SourceBoundary dimension) :
    ‖integerBoundaryEmbedding paid field‖ ≤ (3 : ℝ) ^ power * ‖field‖ :=
  sequenceMultiplierValue_bound _ _ (by positivity) (fun mode => by
    rw [Complex.norm_real, Real.norm_of_nonneg (integerBoundaryRatio_nonnegative grade power mode)]
    exact integerBoundaryRatio_bound paid mode) field

theorem integerBoundaryRatio_weight {grade power : ℕ} (parameters : PhaseParameters) (mode : ℤ × ℤ) :
    integerBoundaryRatio grade power mode * boundaryWeight parameters grade mode =
      sourceBoundaryWeight parameters power mode := by
  have rootNonzero : Real.sqrt (boundaryFrequency mode ^ (2 * grade - 1)) ≠ 0 :=
    (Real.sqrt_pos.2 (pow_pos (boundaryFrequency_pos mode) _)).ne'
  unfold integerBoundaryRatio boundaryWeight sourceBoundaryWeight
  field_simp

theorem integerBoundaryEmbedding_coefficient {dimension grade power : ℕ}
    (parameters : PhaseParameters) (paid : power + 1 ≤ grade)
    (field : BoundaryGrade parameters (ComplexEuclidean dimension) grade) (mode : ℤ × ℤ) :
    sourceBoundaryCoefficient parameters power (integerBoundaryEmbedding paid field) mode =
      boundaryCoefficient parameters grade field mode := by
  have equality : (sourceBoundaryWeight parameters power mode : ℂ) •
      sourceBoundaryCoefficient parameters power (integerBoundaryEmbedding paid field) mode =
      (sourceBoundaryWeight parameters power mode : ℂ) • boundaryCoefficient parameters grade field mode := by
    rw [sourceBoundary_weighted]
    change (integerBoundaryRatio grade power mode : ℂ) • field mode = _
    rw [← boundary_weighted_coefficient parameters grade field mode, smul_smul]
    rw [← Complex.ofReal_mul, integerBoundaryRatio_weight]
  have nonzero : (sourceBoundaryWeight parameters power mode : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sourceBoundaryWeight_pos parameters power mode).ne'
  have cancelled := congrArg (fun value => (sourceBoundaryWeight parameters power mode : ℂ)⁻¹ • value) equality
  simpa only [smul_smul, inv_mul_cancel₀ nonzero, one_smul] using cancelled

def integerSourceTrace {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ) :
    AGrade parameters dimension (power + 1) →L[ℂ] SourceBoundary dimension :=
  (integerBoundaryEmbedding (grade := power + 1) (power := power) le_rfl).comp
    (completedTrace parameters (power + 1) (by omega))

theorem integerSourceTrace_bound {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (field : AGrade parameters dimension (power + 1)) :
    ‖integerSourceTrace parameters power field‖ ≤
      ((3 : ℝ) ^ power * Real.sqrt (traceCellConstant (power + 1))) * ‖field‖ := by
  change ‖integerBoundaryEmbedding le_rfl (completedTrace parameters (power + 1) (by omega) field)‖ ≤ _
  exact (integerBoundaryEmbedding_bound le_rfl _).trans
    ((mul_le_mul_of_nonneg_left (completedTrace_apply_norm_le parameters (power + 1) (by omega) field)
      (by positivity : 0 ≤ (3 : ℝ) ^ power)).trans_eq (mul_assoc _ _ _).symm)

theorem integerSourceTrace_core {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (field : GradeCore parameters dimension (power + 1)) (mode : ℤ × ℤ) :
    sourceBoundaryCoefficient parameters power (integerSourceTrace parameters power (aGradeEta parameters field)) mode =
      originalBoundaryCoefficient parameters field.toCore mode := by
  rw [integerSourceTrace, ContinuousLinearMap.comp_apply,
    integerBoundaryEmbedding_coefficient, completedTrace_coefficient]

theorem sourceBoundary_norm_sq {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (field : SourceBoundary dimension) :
    ‖field‖ ^ 2 = ∑' mode : ℤ × ℤ, Real.exp (2 * boundaryPhase parameters mode.2) *
      annularFrequency mode.1 mode.2 ^ (2 * power) * ‖sourceBoundaryCoefficient parameters power field mode‖ ^ 2 := by
  have equality := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at equality
  rw [equality]
  apply tsum_congr
  intro mode
  rw [← sourceBoundary_weighted parameters power field mode, norm_smul,
    Complex.norm_real, Real.norm_of_nonneg (sourceBoundaryWeight_pos parameters power mode).le,
    sourceBoundaryWeight, mul_pow, mul_pow, ← pow_mul]
  rw [show (2 : ℝ) * boundaryPhase parameters mode.2 = boundaryPhase parameters mode.2 + boundaryPhase parameters mode.2 by ring,
    Real.exp_add, pow_two]
  simp only [Nat.mul_comm power 2]

end Grad.SourceBoundaryTrace
