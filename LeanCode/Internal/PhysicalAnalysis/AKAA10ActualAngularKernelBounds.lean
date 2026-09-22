import AKAA9ActualAngularKernelData

noncomputable section

set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped BigOperators ContDiff

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Algebra
open Grad.GenericCarriers Grad.ActualAngularInverse Grad.Constraints

theorem startupAngularKernel_bound (dimension : ℕ) (weight : ℝ → ℂ)
    (smooth : ContDiff ℝ ∞ weight) (bound : ℝ)
    (bounded : ∀ angle ∈ Icc (0 : ℝ) (2 * Real.pi), ‖weight angle‖ ≤ bound) :
    ‖startupAngularKernel dimension weight smooth‖ ≤
      bound * ‖ContinuousLinearMap.id ℂ (PhysicalValue dimension)‖ := by
  have positive : 0 < 2 * Real.pi := by positivity
  have mass : volume.real (Icc (0 : ℝ) (2 * Real.pi)) = 2 * Real.pi := by
    simp [Measure.real, Real.volume_Icc, Real.pi_pos.le]
  apply (startupAngularKernel_norm dimension weight smooth).trans
  calc
    _ ≤ ∫ _angle in Icc (0 : ℝ) (2 * Real.pi),
        (2 * Real.pi)⁻¹ * (bound * ‖ContinuousLinearMap.id ℂ (PhysicalValue dimension)‖) := by
      apply setIntegral_mono_on
        (startupAngularCoefficient_continuous dimension weight smooth).norm.continuousOn.integrableOn_Icc
        continuous_const.continuousOn.integrableOn_Icc measurableSet_Icc
      intro angle inside
      change ‖(((_ : ℝ) : ℂ)) • (weight angle • ContinuousLinearMap.id ℂ (PhysicalValue dimension))‖ ≤ _
      rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr positive.le)]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (bounded angle inside) (norm_nonneg _))
        (inv_nonneg.mpr positive.le)
    _ = _ := by
      rw [setIntegral_const]
      change volume.real _ * _ = _
      rw [mass, ← mul_assoc, mul_inv_cancel₀ positive.ne', one_mul]

theorem startupCharacterKernel_bound (dimension : ℕ) (mode : ℤ) :
    ‖startupCharacterKernel dimension mode‖ ≤ ‖ContinuousLinearMap.id ℂ (PhysicalValue dimension)‖ := by
  exact (startupAngularKernel_bound dimension (angularCharacter mode) (angularCharacter_smooth mode)
    1 (fun angle _ => (angularCharacter_norm mode angle).le)).trans_eq (one_mul _)

theorem startupPrimitiveKernel_bound (dimension : ℕ) (shift : ℤ) :
    ‖startupPrimitiveKernel dimension shift‖ ≤
      (2 * Real.pi) * ‖ContinuousLinearMap.id ℂ (PhysicalValue dimension)‖ :=
  startupAngularKernel_bound dimension (shiftPrimitiveKernel shift) (shiftPrimitiveKernel_smooth shift)
    (2 * Real.pi) (shiftPrimitiveKernel_bound shift)

end Grad.GaugeCoefficients.Physical.RadialLedger
