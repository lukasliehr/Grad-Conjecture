import GC21Summation

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Grad.GaugeCoefficients.Physical.WeightedTrace

open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.BoundaryTrace

theorem apCoreBoundaryCoefficient_add {dimension : ℕ}
    (first second : ℤ →₀ ClosedJet dimension) (mode : ℤ × ℤ) :
    apCoreBoundaryCoefficient (first + second) mode =
      apCoreBoundaryCoefficient first mode + apCoreBoundaryCoefficient second mode := by
  change fourierCoeff (fun angle : CellCircle =>
    (first mode.2).value (boundaryDiskPoint angle) + (second mode.2).value (boundaryDiskPoint angle)) mode.1 = _
  unfold apCoreBoundaryCoefficient fourierCoeff
  simp only [smul_add]
  apply integral_add
  · exact ((fourier _).continuous.smul ((first mode.2).value.continuous.comp
      boundaryDiskPoint_continuous)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact ((fourier _).continuous.smul ((second mode.2).value.continuous.comp
      boundaryDiskPoint_continuous)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem apCoreBoundaryCoefficient_smul {dimension : ℕ}
    (scalar : ℂ) (field : ℤ →₀ ClosedJet dimension) (mode : ℤ × ℤ) :
    apCoreBoundaryCoefficient (scalar • field) mode = scalar • apCoreBoundaryCoefficient field mode := by
  change fourierCoeff (fun angle : CellCircle =>
    scalar • (field mode.2).value (boundaryDiskPoint angle)) mode.1 = _
  unfold apCoreBoundaryCoefficient fourierCoeff
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with angle
  exact smul_comm _ _ _

def apTraceCoordinates {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : ℤ →₀ ClosedJet dimension) (mode : ℤ × ℤ) : PhysicalValue dimension :=
  (apBoundaryWeight L sigma gamma ell grade mode : ℂ) • apCoreBoundaryCoefficient field mode

theorem apTraceCoordinates_norm_sq {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : ℤ →₀ ClosedJet dimension) (mode : ℤ × ℤ) :
    ‖apTraceCoordinates L sigma gamma ell grade field mode‖ ^ 2 =
      apBoundaryEnergy L sigma gamma ell grade field mode := by
  rw [apTraceCoordinates, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (apBoundaryWeight_pos L sigma gamma ell grade mode)]
  unfold apBoundaryWeight apBoundaryEnergy
  simp only [mul_pow, Real.sq_sqrt (pow_nonneg (apBoundaryFrequency_pos L ell _).le _)]
  rw [show Real.exp (apBoundaryPhase sigma gamma ell mode.2) ^ 2 =
    Real.exp (2 * apBoundaryPhase sigma gamma ell mode.2) by rw [two_mul, Real.exp_add, pow_two]]

theorem apTraceCoordinates_memlp {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (field : ℤ →₀ ClosedJet dimension) :
    Memℓp (apTraceCoordinates L sigma gamma ell grade field) 2 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat, apTraceCoordinates_norm_sq]
  exact apBoundary_summable L sigma gamma ell grade gradePositive field

def apCoreTraceLinear {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (gradePositive : 1 ≤ grade) :
    (ℤ →₀ ClosedJet dimension) →ₗ[ℂ] APBoundaryGrade L sigma gamma ell dimension grade where
  toFun field := ⟨apTraceCoordinates L sigma gamma ell grade field,
    apTraceCoordinates_memlp L sigma gamma ell grade gradePositive field⟩
  map_add' first second := by
    apply Subtype.ext
    funext mode
    change apTraceCoordinates L sigma gamma ell grade (first + second) mode =
      apTraceCoordinates L sigma gamma ell grade first mode + apTraceCoordinates L sigma gamma ell grade second mode
    rw [apTraceCoordinates, apCoreBoundaryCoefficient_add, smul_add]
    rfl
  map_smul' scalar field := by
    apply Subtype.ext
    funext mode
    change apTraceCoordinates L sigma gamma ell grade (scalar • field) mode =
      scalar • apTraceCoordinates L sigma gamma ell grade field mode
    rw [apTraceCoordinates, apCoreBoundaryCoefficient_smul, apTraceCoordinates, smul_comm]

theorem apCoreTraceLinear_coefficient {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (field : ℤ →₀ ClosedJet dimension) (mode : ℤ × ℤ) :
    apBoundaryCoefficient L sigma gamma ell grade (apCoreTraceLinear L sigma gamma ell grade gradePositive field) mode =
      apCoreBoundaryCoefficient field mode := by
  change ((apBoundaryWeight L sigma gamma ell grade mode : ℂ)⁻¹) •
    ((apBoundaryWeight L sigma gamma ell grade mode : ℂ) • apCoreBoundaryCoefficient field mode) = _
  exact inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (apBoundaryWeight_pos L sigma gamma ell grade mode).ne') _

theorem apCoreTraceLinear_norm_sq_le {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (field : ℤ →₀ ClosedJet dimension) :
    ‖apCoreTraceLinear L sigma gamma ell grade gradePositive field‖ ^ 2 ≤
      traceCellConstant grade * ‖apFiniteInto (grade := grade) L sigma gamma ell field‖ ^ 2 := by
  rw [apBoundary_norm_sq L sigma gamma ell grade]
  simp only [apCoreTraceLinear_coefficient]
  exact apBoundary_bound L sigma gamma ell grade gradePositive field

theorem apCoreTraceLinear_norm_le {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (field : ℤ →₀ ClosedJet dimension) :
    ‖apCoreTraceLinear L sigma gamma ell grade gradePositive field‖ ≤
      Real.sqrt (traceCellConstant grade) * ‖apFiniteInto (grade := grade) L sigma gamma ell field‖ := by
  have bound := Real.sqrt_le_sqrt (apCoreTraceLinear_norm_sq_le L sigma gamma ell grade gradePositive field)
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_mul (traceCellConstant_nonnegative grade)] using bound

end Grad.GaugeCoefficients.Physical.WeightedTrace
