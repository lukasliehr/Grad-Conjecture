import ANS5NativeKernelBound

noncomputable section
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.ActualAngularInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.GaugeCoefficients.Radial Grad.PhysicalFamily Grad.FourierGrade Grad.ActualSmoothPDE

theorem kernelRotationJet_add {dimension : ℕ} (weight : ℝ → ℂ)
    (smooth : ContDiff ℝ ∞ weight) (first second : ClosedJet dimension) :
    kernelRotationJet weight smooth (first + second) =
      kernelRotationJet weight smooth first + kernelRotationJet weight smooth second := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simp only [kernelRotationJet_value, closedJet_value_add, ContinuousMap.add_apply, smul_add]
  rw [integral_add]
  · exact smul_add _ _ _
  · exact ((smooth.continuous).smul
      (by simpa using angularValueIntegrand_continuous 0 first point)).continuousOn.integrableOn_Icc
  · exact ((smooth.continuous).smul
      (by simpa using angularValueIntegrand_continuous 0 second point)).continuousOn.integrableOn_Icc

theorem kernelRotationJet_smul {dimension : ℕ} (weight : ℝ → ℂ)
    (smooth : ContDiff ℝ ∞ weight) (scalar : ℂ) (field : ClosedJet dimension) :
    kernelRotationJet weight smooth (scalar • field) = scalar • kernelRotationJet weight smooth field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change (kernelRotationJet weight smooth (scalar • field)).value point =
    scalar • (kernelRotationJet weight smooth field).value point
  simp_rw [kernelRotationJet_value]
  change (2 * Real.pi)⁻¹ • (∫ angle in Icc (0 : ℝ) (2 * Real.pi),
    weight angle • (scalar • field.value (rotatedPoint angle point))) = _
  simp_rw [smul_comm _ scalar]
  rw [integral_smul, smul_comm]

def kernelRotationLinear (dimension : ℕ) (weight : ℝ → ℂ)
    (smooth : ContDiff ℝ ∞ weight) : ClosedJet dimension →ₗ[ℂ] ClosedJet dimension where
  toFun := kernelRotationJet weight smooth
  map_add' := kernelRotationJet_add weight smooth
  map_smul' := kernelRotationJet_smul weight smooth

/-- Compact angular primitive for R+i*shift; the resonant mode is removed below. -/
def shiftPrimitiveKernel (shift : ℤ) (angle : ℝ) : ℂ :=
  (angle : ℂ) * angularCharacter (-shift) angle

theorem shiftPrimitiveKernel_smooth (shift : ℤ) : ContDiff ℝ ∞ (shiftPrimitiveKernel shift) :=
  Complex.ofRealCLM.contDiff.mul (angularCharacter_smooth (-shift))

theorem shiftPrimitiveKernel_bound (shift : ℤ) (angle : ℝ)
    (inside : angle ∈ Icc (0 : ℝ) (2 * Real.pi)) : ‖shiftPrimitiveKernel shift angle‖ ≤ 2 * Real.pi := by
  rw [shiftPrimitiveKernel, norm_mul, angularCharacter_norm, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg inside.1]
  exact inside.2

theorem shiftKernel_pureMode {dimension : ℕ} (shift mode : ℤ) (nonzero : mode + shift ≠ 0)
    (field : ClosedJet dimension) :
    kernelRotationJet (shiftPrimitiveKernel shift) (shiftPrimitiveKernel_smooth shift)
      (angularClosedJet mode field) =
      (Complex.I * ((mode + shift : ℤ) : ℂ))⁻¹ • angularClosedJet mode field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change (kernelRotationJet _ _ (angularClosedJet mode field)).value point =
    (Complex.I * ((mode + shift : ℤ) : ℂ))⁻¹ • (angularClosedJet mode field).value point
  rw [kernelRotationJet_value]
  simp_rw [angularClosedJet_rotation_value, angularCharacter_neg_angle]
  have row (angle : ℝ) : shiftPrimitiveKernel shift angle •
      (angularCharacter (-mode) angle • (angularClosedJet mode field).value point) =
      ((angle : ℂ) * cellExponential (mode + shift) angle) •
        (angularClosedJet mode field).value point := by
    rw [shiftPrimitiveKernel, smul_smul, mul_assoc, angularCharacter_mul]
    congr 2
    simp only [angularCharacter, neg_add_rev, neg_neg]
  simp_rw [row]
  rw [integral_smul_const, ← smul_assoc, angularPrimitive_scalar_integral (mode + shift) nonzero]

/-- Actual angular inverse, zero on the unique resonant Fourier mode. -/
def shiftInverseLinear (dimension : ℕ) (shift : ℤ) : ClosedJet dimension →ₗ[ℂ] ClosedJet dimension :=
  (kernelRotationLinear dimension (shiftPrimitiveKernel shift) (shiftPrimitiveKernel_smooth shift)).comp
    (excludedAngularJetLinear dimension {-shift})

def shiftInverseJet {dimension : ℕ} (shift : ℤ) (field : ClosedJet dimension) : ClosedJet dimension :=
  shiftInverseLinear dimension shift field

theorem shiftInverseJet_coefficient {dimension : ℕ} (shift mode : ℤ) (field : ClosedJet dimension) :
    angularClosedJet mode (shiftInverseJet shift field) =
      if mode = -shift then 0 else
        (Complex.I * ((mode + shift : ℤ) : ℂ))⁻¹ • angularClosedJet mode field := by
  change angularClosedJet mode (kernelRotationJet (shiftPrimitiveKernel shift)
    (shiftPrimitiveKernel_smooth shift) (excludedAngularJet {-shift} field)) = _
  rw [angularClosedJet_kernelRotation]
  have coefficient : angularClosedJet mode (excludedAngularJet {-shift} field) =
      if mode = -shift then 0 else angularClosedJet mode field := by
    change angularClosedJetLinear dimension mode (field - selectedAngularJet {-shift} field) = _
    rw [map_sub]
    change angularClosedJet mode field - angularClosedJet mode (selectedAngularJet {-shift} field) = _
    rw [angularClosedJet_selected]
    by_cases resonant : mode = -shift <;> simp [resonant]
  rw [coefficient]
  by_cases resonant : mode = -shift
  · rw [if_pos resonant, if_pos resonant]
    exact map_zero (kernelRotationLinear dimension (shiftPrimitiveKernel shift) (shiftPrimitiveKernel_smooth shift))
  · rw [if_neg resonant, if_neg resonant]
    exact shiftKernel_pureMode shift mode (by omega) field

end Grad.ActualAngularInverse
