import RotationAverageAlgebra

noncomputable section

open Set MeasureTheory
open scoped ContDiff Interval Topology

namespace Grad.Constraints

open Grad.MainTarget Grad.PhysicalFamily Grad.GaugeCoefficients.Radial

def physicalRotationLinear (angle : ℝ) : Plane →L[ℝ] Plane :=
  (planeRotationEquiv angle).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem physicalRotationLinear_apply (angle : ℝ) (point : Plane) :
    physicalRotationLinear angle point = planeRotationAction angle point :=
  (physicalRotation_eq_orthogonal angle point).symm

variable {Value : Type} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
  [CompleteSpace Value]

omit [CompleteSpace Value] in
theorem rotationIntegrand_smooth {field : Plane → Value} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ field (Metric.ball 0 radius)) :
    ContDiffOn ℝ ∞
      (fun argument : Plane × ℝ => field (planeRotationAction argument.2 argument.1))
      (Metric.ball 0 radius ×ˢ univ) := by
  apply smooth.comp (physicalRotation_contDiff.comp
    (contDiff_snd.prodMk contDiff_fst)).contDiffOn
  intro argument argumentIn
  simpa [Metric.mem_ball, dist_zero_right] using argumentIn.1

omit [CompleteSpace Value] in
theorem rotationAverage_euler {field : Plane → Value} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ field (Metric.ball 0 radius))
    {point : Plane} (pointIn : point ∈ Metric.ball (0 : Plane) radius) :
    fderiv ℝ (rotationAverage field) point point =
      rotationAverage (fun argument => fderiv ℝ field argument argument) point := by
  let integrand : Plane × ℝ → Value := fun argument =>
    field (planeRotationAction argument.2 argument.1)
  have integrandSmooth : ContDiffOn ℝ ∞ integrand (Metric.ball 0 radius ×ˢ univ) :=
    rotationIntegrand_smooth smooth
  have derivativeContinuous : Continuous (fun angle =>
      integralParameterDerivative integrand (point, angle)) :=
    (integralParameterDerivative_smooth Metric.isOpen_ball integrandSmooth).continuousOn.comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨pointIn, mem_univ _⟩)
  have averageDerivative : HasFDerivAt (rotationAverage field)
      ((2 * Real.pi)⁻¹ • ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
        integralParameterDerivative integrand (point, angle)) point := by
    convert! (hasFDerivAt_compactIntegral Metric.isOpen_ball integrandSmooth
      (0 : ℝ) (2 * Real.pi) point pointIn).const_smul ((2 * Real.pi)⁻¹) using 1
    ext argument
    exact rotationAverage_eq_compactIntegral field argument
  rw [averageDerivative.fderiv, smul_apply,
    ContinuousLinearMap.integral_apply derivativeContinuous.continuousOn.integrableOn_Icc,
    rotationAverage_eq_compactIntegral]
  congr 1
  apply integral_congr_ae
  filter_upwards with angle
  have rotatedIn : planeRotationAction angle point ∈ Metric.ball (0 : Plane) radius := by
    simpa [Metric.mem_ball, dist_zero_right] using pointIn
  have fieldDerivative := (smooth.contDiffAt
    (Metric.isOpen_ball.mem_nhds rotatedIn)).differentiableAt (by simp)
  have rotatedDerivative : HasFDerivAt
      (fun argument => field (planeRotationAction angle argument))
      ((fderiv ℝ field (planeRotationAction angle point)).comp (physicalRotationLinear angle)) point := by
    have innerDerivative : HasFDerivAt (planeRotationAction angle)
        (physicalRotationLinear angle) point := by
      convert! (physicalRotationLinear angle).hasFDerivAt (x := point) using 1
      funext argument
      exact (physicalRotationLinear_apply angle argument).symm
    exact fieldDerivative.hasFDerivAt.comp point innerDerivative
  have integrandDifferentiable := (integrandSmooth.contDiffAt
    ((Metric.isOpen_ball.prod isOpen_univ).mem_nhds
      (show (point, angle) ∈ Metric.ball 0 radius ×ˢ (univ : Set ℝ) from
        ⟨pointIn, mem_univ _⟩))).differentiableAt (by simp)
  rw [integralParameterDerivative_eq point angle integrandDifferentiable]
  change (fderiv ℝ (fun argument => field (planeRotationAction angle argument)) point) point = _
  rw [rotatedDerivative.fderiv]
  simp only [ContinuousLinearMap.comp_apply, physicalRotationLinear_apply]

end Grad.Constraints
