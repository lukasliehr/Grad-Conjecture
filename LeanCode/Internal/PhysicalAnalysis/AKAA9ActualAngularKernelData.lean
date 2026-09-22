import AKAA8FixedOrthogonalFullCellKernel

noncomputable section

set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped BigOperators ContDiff

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Algebra
open Grad.GenericCarriers Grad.ActualAngularInverse Grad.Constraints

def startupAngularCoefficient (dimension : ℕ) (weight : ℝ → ℂ) (angle : ℝ) :
    OperatorValue dimension dimension :=
  (((2 * Real.pi)⁻¹ : ℝ) : ℂ) • (weight angle • ContinuousLinearMap.id ℂ (PhysicalValue dimension))

theorem startupAngularCoefficient_continuous (dimension : ℕ) (weight : ℝ → ℂ)
    (smooth : ContDiff ℝ ∞ weight) : Continuous (startupAngularCoefficient dimension weight) := by
  unfold startupAngularCoefficient
  exact (smooth.continuous.smul
    (continuous_const (y := ContinuousLinearMap.id ℂ (PhysicalValue dimension)))).const_smul
      (((2 * Real.pi)⁻¹ : ℝ) : ℂ)

def startupAngularKernelData (dimension : ℕ) (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight) :
    Grad.FullCellKernel.L2KernelData (volume.restrict (Icc (0 : ℝ) (2 * Real.pi)))
      dimension dimension openUnitDisk :=
  startupFixedKernelData (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) planeRotationEquiv
    (fun angle => by
      intro point
      change (‖planeRotationEquiv angle point‖ < 1 ↔ ‖point‖ < 1)
      rw [(planeRotationEquiv angle).norm_map])
    continuous_planeRotation_joint.measurable (startupAngularCoefficient dimension weight)
    (startupAngularCoefficient_continuous dimension weight smooth).measurable
    (startupAngularCoefficient_continuous dimension weight smooth).integrableOn_Icc

def startupAngularKernel (dimension : ℕ) (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight) :=
  Grad.FullCellKernel.kernel (startupAngularKernelData dimension weight smooth)

theorem startupAngularKernel_norm (dimension : ℕ) (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight) :
    ‖startupAngularKernel dimension weight smooth‖ ≤
      ∫ angle in Icc (0 : ℝ) (2 * Real.pi), ‖startupAngularCoefficient dimension weight angle‖ := by
  have bound := Grad.FullCellKernel.kernel_norm_le (startupAngularKernelData dimension weight smooth)
  change ‖startupAngularKernel dimension weight smooth‖ ≤ Real.sqrt
    ((∫ angle in Icc (0 : ℝ) (2 * Real.pi), ‖startupAngularCoefficient dimension weight angle‖) *
     (∫ angle in Icc (0 : ℝ) (2 * Real.pi), ‖startupAngularCoefficient dimension weight angle‖)) at bound
  simpa only [Real.sqrt_mul_self (integral_nonneg (fun _ => norm_nonneg _))] using bound

/-- Every integer angular character is retained, including ±1 and ±2. -/
def startupCharacterKernel (dimension : ℕ) (mode : ℤ) :=
  startupAngularKernel dimension (angularCharacter mode) (angularCharacter_smooth mode)

/-- The literal compact primitive in the accepted true angular inverse.
 Its resonant subtraction is separate and unchanged. -/
def startupPrimitiveKernel (dimension : ℕ) (shift : ℤ) :=
  startupAngularKernel dimension (shiftPrimitiveKernel shift) (shiftPrimitiveKernel_smooth shift)

theorem startupAngularKernel_coefficient (dimension : ℕ) (weight : ℝ → ℂ)
    (smooth : ContDiff ℝ ∞ weight) (output input : ℤ)
    (angle : ℝ) (point : Grad.PDEBootstrap.Spatial) :
    (startupAngularKernelData dimension weight smooth).coefficient output input (angle, point) =
      if output = input then startupAngularCoefficient dimension weight angle else 0 := rfl

end Grad.GaugeCoefficients.Physical.RadialLedger
