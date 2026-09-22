import BT18Summation

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Grad.BoundaryTrace

open Grad.ClosedJets Grad.CartesianState

theorem originalBoundaryCoefficient_add {dimension : ℕ} (parameters : PhaseParameters)
    (first second : ACore parameters dimension) (mode : ℤ × ℤ) :
    originalBoundaryCoefficient parameters (first + second) mode =
      originalBoundaryCoefficient parameters first mode + originalBoundaryCoefficient parameters second mode := by
  change fourierCoeff (fun angle : CellCircle =>
    (first.1 mode.2).value (boundaryDiskPoint angle) + (second.1 mode.2).value (boundaryDiskPoint angle)) mode.1 = _
  unfold originalBoundaryCoefficient fourierCoeff
  simp only [smul_add]
  apply integral_add
  · exact ((fourier _).continuous.smul ((first.1 mode.2).value.continuous.comp
      boundaryDiskPoint_continuous)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact ((fourier _).continuous.smul ((second.1 mode.2).value.continuous.comp
      boundaryDiskPoint_continuous)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem originalBoundaryCoefficient_smul {dimension : ℕ} (parameters : PhaseParameters)
    (scalar : ℂ) (field : ACore parameters dimension) (mode : ℤ × ℤ) :
    originalBoundaryCoefficient parameters (scalar • field) mode =
      scalar • originalBoundaryCoefficient parameters field mode := by
  change fourierCoeff (fun angle : CellCircle =>
    scalar • (field.1 mode.2).value (boundaryDiskPoint angle)) mode.1 = _
  unfold originalBoundaryCoefficient fourierCoeff
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with angle
  exact smul_comm _ _ _

def traceCoordinates {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (field : ACore parameters dimension) (mode : ℤ × ℤ) : ComplexEuclidean dimension :=
  (boundaryWeight parameters grade mode : ℂ) • originalBoundaryCoefficient parameters field mode

theorem traceCoordinates_norm_sq {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (field : ACore parameters dimension) (mode : ℤ × ℤ) :
    ‖traceCoordinates parameters grade field mode‖ ^ 2 =
      originalBoundaryEnergy parameters grade field mode := by
  rw [traceCoordinates, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (boundaryWeight_pos parameters grade mode)]
  unfold boundaryWeight originalBoundaryEnergy
  simp only [mul_pow, Real.sq_sqrt (pow_nonneg (boundaryFrequency_pos _).le _)]
  rw [show Real.exp (boundaryPhase parameters mode.2) ^ 2 =
    Real.exp (2 * boundaryPhase parameters mode.2) by rw [two_mul, Real.exp_add, pow_two]]

theorem traceCoordinates_memlp {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (field : ACore parameters dimension) :
    Memℓp (traceCoordinates parameters grade field) 2 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat, traceCoordinates_norm_sq]
  exact original_boundary_summable parameters grade gradePositive field

/-- The literal weighted original boundary coefficients, not the coefficients of W_gamma h. -/
def coreTraceLinear {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) :
    GradeCore parameters dimension grade →ₗ[ℂ] BoundaryGrade parameters (ComplexEuclidean dimension) grade where
  toFun field := ⟨traceCoordinates parameters grade field.toCore,
    traceCoordinates_memlp parameters grade gradePositive field.toCore⟩
  map_add' first second := by
    apply Subtype.ext
    funext mode
    change traceCoordinates parameters grade (first.toCore + second.toCore) mode =
      traceCoordinates parameters grade first.toCore mode + traceCoordinates parameters grade second.toCore mode
    rw [traceCoordinates, originalBoundaryCoefficient_add, smul_add]
    rfl
  map_smul' scalar field := by
    apply Subtype.ext
    funext mode
    change traceCoordinates parameters grade (scalar • field.toCore) mode =
      scalar • traceCoordinates parameters grade field.toCore mode
    rw [traceCoordinates, originalBoundaryCoefficient_smul, traceCoordinates, smul_comm]

theorem coreTraceLinear_coefficient {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (field : GradeCore parameters dimension grade) (mode : ℤ × ℤ) :
    boundaryCoefficient parameters grade (coreTraceLinear parameters grade gradePositive field) mode =
      originalBoundaryCoefficient parameters field.toCore mode := by
  change ((boundaryWeight parameters grade mode : ℂ)⁻¹) •
    ((boundaryWeight parameters grade mode : ℂ) • originalBoundaryCoefficient parameters field.toCore mode) = _
  exact inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (boundaryWeight_pos parameters grade mode).ne') _

theorem coreTraceLinear_norm_sq_le {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (field : GradeCore parameters dimension grade) :
    ‖coreTraceLinear parameters grade gradePositive field‖ ^ 2 ≤ traceCellConstant grade * ‖field‖ ^ 2 := by
  rw [boundary_norm_sq]
  simp only [coreTraceLinear_coefficient]
  exact original_boundary_bound parameters grade gradePositive field.toCore

theorem coreTraceLinear_norm_le {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (field : GradeCore parameters dimension grade) :
    ‖coreTraceLinear parameters grade gradePositive field‖ ≤ Real.sqrt (traceCellConstant grade) * ‖field‖ := by
  have bound := Real.sqrt_le_sqrt (coreTraceLinear_norm_sq_le parameters grade gradePositive field)
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_mul (traceCellConstant_nonnegative grade)] using bound

end Grad.BoundaryTrace
