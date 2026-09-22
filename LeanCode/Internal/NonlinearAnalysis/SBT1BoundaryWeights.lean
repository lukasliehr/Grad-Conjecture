import RSC13PublicRestriction

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.SourceBoundaryTrace
open Grad.SourceCollarDivision Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace

abbrev SourceBoundary (dimension : ℕ) := lp (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2

def sequenceMultiplierValue {dimension : ℕ} (coefficient : ℤ × ℤ → ℂ)
    (constant : ℝ) (nonnegative : 0 ≤ constant) (bound : ∀ mode, ‖coefficient mode‖ ≤ constant)
    (field : SourceBoundary dimension) : SourceBoundary dimension :=
  ⟨fun mode => coefficient mode • field mode, by
    let comparison := (constant : ℂ) • field
    apply (lp.memℓp comparison).mono'
    intro mode
    change ‖coefficient mode • field mode‖ ≤ ‖(constant : ℂ) • field mode‖
    rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg nonnegative]
    exact mul_le_mul_of_nonneg_right (bound mode) (norm_nonneg _)⟩

theorem sequenceMultiplierValue_bound {dimension : ℕ} (coefficient : ℤ × ℤ → ℂ)
    (constant : ℝ) (nonnegative : 0 ≤ constant) (bound : ∀ mode, ‖coefficient mode‖ ≤ constant)
    (field : SourceBoundary dimension) :
    ‖sequenceMultiplierValue coefficient constant nonnegative bound field‖ ≤ constant * ‖field‖ := by
  calc
    _ ≤ ‖(constant : ℂ) • field‖ := by
      apply lp.norm_mono (by norm_num)
      intro mode
      change ‖coefficient mode • field mode‖ ≤ ‖(constant : ℂ) • field mode‖
      rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg nonnegative]
      exact mul_le_mul_of_nonneg_right (bound mode) (norm_nonneg _)
    _ = _ := by rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg nonnegative]

def sequenceMultiplier {dimension : ℕ} (coefficient : ℤ × ℤ → ℂ)
    (constant : ℝ) (nonnegative : 0 ≤ constant) (bound : ∀ mode, ‖coefficient mode‖ ≤ constant) :
    SourceBoundary dimension →L[ℂ] SourceBoundary dimension :=
  LinearMap.mkContinuous
    { toFun := sequenceMultiplierValue coefficient constant nonnegative bound
      map_add' := fun first second => by
        apply lp.ext
        funext mode
        exact smul_add _ _ _
      map_smul' := fun scalar field => by
        apply lp.ext
        funext mode
        exact smul_comm (coefficient mode) scalar (field mode) }
    constant (sequenceMultiplierValue_bound coefficient constant nonnegative bound)

theorem sequenceMultiplier_apply {dimension : ℕ} (coefficient : ℤ × ℤ → ℂ)
    (constant : ℝ) (nonnegative : 0 ≤ constant) (bound : ∀ mode, ‖coefficient mode‖ ≤ constant)
    (field : SourceBoundary dimension) (mode : ℤ × ℤ) :
    sequenceMultiplier coefficient constant nonnegative bound field mode = coefficient mode • field mode := rfl

theorem annularFrequency_pos (mode : ℤ × ℤ) : 0 < annularFrequency mode.1 mode.2 := by
  unfold annularFrequency
  positivity

theorem annularFrequency_le_three (mode : ℤ × ℤ) :
    annularFrequency mode.1 mode.2 ≤ 3 * boundaryFrequency mode := by
  have angular : |(mode.1 : ℝ)| ≤ boundaryFrequency mode := by
    rw [boundaryFrequency, ← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (mode.2 : ℝ)]
  have cell : |(mode.2 : ℝ)| ≤ boundaryFrequency mode := by
    rw [boundaryFrequency, ← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (mode.1 : ℝ)]
  unfold annularFrequency
  linarith [boundaryFrequency_one_le mode]

def integerBoundaryRatio (grade power : ℕ) (mode : ℤ × ℤ) : ℝ :=
  annularFrequency mode.1 mode.2 ^ power / Real.sqrt (boundaryFrequency mode ^ (2 * grade - 1))

theorem integerBoundaryRatio_nonnegative (grade power : ℕ) (mode : ℤ × ℤ) :
    0 ≤ integerBoundaryRatio grade power mode :=
  div_nonneg (pow_nonneg (annularFrequency_pos mode).le _) (Real.sqrt_nonneg _)

theorem integerBoundaryRatio_bound {grade power : ℕ} (paid : power + 1 ≤ grade) (mode : ℤ × ℤ) :
    integerBoundaryRatio grade power mode ≤ (3 : ℝ) ^ power := by
  have rootPositive : 0 < Real.sqrt (boundaryFrequency mode ^ (2 * grade - 1)) :=
    Real.sqrt_pos.2 (pow_pos (boundaryFrequency_pos mode) _)
  have rootBound : boundaryFrequency mode ^ power ≤ Real.sqrt (boundaryFrequency mode ^ (2 * grade - 1)) := by
    have squareBound : (boundaryFrequency mode ^ power) ^ 2 ≤ boundaryFrequency mode ^ (2 * grade - 1) := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ (boundaryFrequency_one_le mode) (by omega)
    simpa only [Real.sqrt_sq (pow_nonneg (boundaryFrequency_pos mode).le _)] using Real.sqrt_le_sqrt squareBound
  rw [integerBoundaryRatio, div_le_iff₀ rootPositive]
  calc
    _ ≤ (3 * boundaryFrequency mode) ^ power :=
      pow_le_pow_left₀ (annularFrequency_pos mode).le (annularFrequency_le_three mode) _
    _ = (3 : ℝ) ^ power * boundaryFrequency mode ^ power := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left rootBound (by positivity)

def sourceBoundaryWeight (parameters : PhaseParameters) (power : ℕ) (mode : ℤ × ℤ) : ℝ :=
  Real.exp (boundaryPhase parameters mode.2) * annularFrequency mode.1 mode.2 ^ power

theorem sourceBoundaryWeight_pos (parameters : PhaseParameters) (power : ℕ) (mode : ℤ × ℤ) :
    0 < sourceBoundaryWeight parameters power mode :=
  mul_pos (Real.exp_pos _) (pow_pos (annularFrequency_pos mode) _)

def sourceBoundaryCoefficient {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (field : SourceBoundary dimension) (mode : ℤ × ℤ) : ComplexEuclidean dimension :=
  ((sourceBoundaryWeight parameters power mode : ℂ)⁻¹) • field mode

theorem sourceBoundary_weighted {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (field : SourceBoundary dimension) (mode : ℤ × ℤ) :
    (sourceBoundaryWeight parameters power mode : ℂ) • sourceBoundaryCoefficient parameters power field mode = field mode :=
  smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr (sourceBoundaryWeight_pos parameters power mode).ne') _

end Grad.SourceBoundaryTrace
