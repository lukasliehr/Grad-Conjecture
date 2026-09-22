import AKBW11UniformRankOperatorAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

open scoped ContDiff

namespace Grad.CartesianStartup
open MeasureTheory Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.GaugeCoefficients.Algebra (OperatorValue)
open Grad.GaugeCoefficients.Physical.RadialLedger

namespace StartupRankOperator

def fixed {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure] {input output : ℕ} (rank : ℕ)
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue input output) (originalIntegrable : Integrable coefficient measure)
    (measurable : Measurable (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter))) :
    StartupRankOperator rank input output := by
  let lifted := fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter)
  have integrable : Integrable lifted measure := startupCovectorCoefficient_integrable
    measure rank orthogonal coefficient originalIntegrable measurable.aestronglyMeasurable
  let data := startupFixedKernelData measure orthogonal invariant actionMeasurable lifted measurable integrable
  have integralBound : (∫ parameter, ‖lifted parameter‖ ∂measure) ≤ ∫ parameter, ‖coefficient parameter‖ ∂measure :=
    integral_mono integrable.norm originalIntegrable.norm (fun parameter => startupCovectorCoefficient_norm rank _ _)
  have bigger : (∫ parameter, ‖coefficient parameter‖ ∂measure) ≤ 7 * ∫ parameter, ‖coefficient parameter‖ ∂measure := by
    have positive : 0 ≤ ∫ parameter, ‖coefficient parameter‖ ∂measure := integral_nonneg (fun _ => norm_nonneg _)
    linarith
  refine {
    coarse := Grad.FullCellKernel.kernel data
    fine := startupFixedFirstGraph measure orthogonal invariant actionMeasurable lifted measurable integrable
    compatible := startupFixedFirstGraph_base measure orthogonal invariant actionMeasurable lifted measurable integrable
    bound := 7 * ∫ parameter, ‖coefficient parameter‖ ∂measure
    nonnegative := mul_nonneg (by norm_num) (integral_nonneg (fun _ => norm_nonneg _))
    coarse_bound := ?_
    fine_bound := (startupFixedFirstGraph_norm measure orthogonal invariant actionMeasurable lifted measurable integrable).trans
      (mul_le_mul_of_nonneg_left integralBound (by norm_num)) }
  have normBound := Grad.FullCellKernel.kernel_norm_le data
  change ‖Grad.FullCellKernel.kernel data‖ ≤ Real.sqrt
    ((∫ parameter, ‖lifted parameter‖ ∂measure) * ∫ parameter, ‖lifted parameter‖ ∂measure) at normBound
  rw [Real.sqrt_mul_self (integral_nonneg (fun _ => norm_nonneg _))] at normBound
  exact normBound.trans (integralBound.trans bigger)

theorem fixed_bound {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure] {input output : ℕ} (rank : ℕ)
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue input output) (originalIntegrable : Integrable coefficient measure)
    (measurable : Measurable (fun parameter => startupCovectorCoefficient rank (orthogonal parameter) (coefficient parameter))) :
    (fixed measure rank orthogonal invariant actionMeasurable coefficient originalIntegrable measurable).bound =
      7 * ∫ parameter, ‖coefficient parameter‖ ∂measure := rfl

def angular (dimension rank : ℕ) (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight) :
    StartupRankOperator rank dimension dimension :=
  fixed (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))) rank Grad.GaugeCoefficients.Radial.planeRotationEquiv
    (fun angle point => by
      change (‖Grad.GaugeCoefficients.Radial.planeRotationEquiv angle point‖ < 1 ↔ ‖point‖ < 1)
      rw [(Grad.GaugeCoefficients.Radial.planeRotationEquiv angle).norm_map])
    Grad.GaugeCoefficients.Radial.continuous_planeRotation_joint.measurable (startupAngularCoefficient dimension weight)
    (startupAngularCoefficient_continuous dimension weight smooth).integrableOn_Icc
    (startupCovectorCoefficient_continuous rank Grad.GaugeCoefficients.Radial.planeRotationEquiv
      Grad.GaugeCoefficients.Radial.continuous_planeRotation_joint (startupAngularCoefficient dimension weight)
      (startupAngularCoefficient_continuous dimension weight smooth)).measurable

def point {input output : ℕ} (rank : ℕ) (mapping : OperatorValue input output)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) : StartupRankOperator rank input output :=
  fixed (Measure.dirac (0 : ℝ)) rank (fun _ => orthogonal)
    (fun _ point => by change (‖orthogonal point‖ < 1 ↔ ‖point‖ < 1); rw [orthogonal.norm_map])
    (orthogonal.continuous.comp continuous_snd).measurable (fun _ => mapping)
    (integrable_const mapping) measurable_const

theorem angular_bound (dimension rank : ℕ) (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight) :
    (angular dimension rank weight smooth).bound =
      7 * ∫ angle in Set.Icc (0 : ℝ) (2 * Real.pi), ‖startupAngularCoefficient dimension weight angle‖ := rfl

theorem point_bound {input output : ℕ} (rank : ℕ) (mapping : OperatorValue input output)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) : (point rank mapping orthogonal).bound = 7 * ‖mapping‖ := by
  change 7 * (∫ _ : ℝ, ‖mapping‖ ∂Measure.dirac (0 : ℝ)) = _
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]

end StartupRankOperator
end Grad.CartesianStartup
