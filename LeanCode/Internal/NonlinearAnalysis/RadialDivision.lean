import RadialIntegralFTC
import RadialDifferential
import LiteralRowAlgebra

noncomputable section

open Set MeasureTheory
open scoped ContDiff Interval Topology

namespace Grad.NonlinearQuotient

open Grad.MainTarget Grad.PhysicalFamily

theorem bilinear_coordinate_expansion
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (bilinear : Plane →L[ℝ] Plane →L[ℝ] Target) (a b c d : ℝ) :
    bilinear (a • diskBasis 0 + b • diskBasis 1) (c • diskBasis 0 + d • diskBasis 1) =
      (a * c) • bilinear (diskBasis 0) (diskBasis 0) +
      (a * d) • bilinear (diskBasis 0) (diskBasis 1) +
      (b * c) • bilinear (diskBasis 1) (diskBasis 0) +
      (b * d) • bilinear (diskBasis 1) (diskBasis 1) := by
  simp
  module

theorem bilinear_radial_trace
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (bilinear : Plane →L[ℝ] Plane →L[ℝ] Target) (point : Plane) :
    bilinear point point + bilinear (planeQuarterTurn point) (planeQuarterTurn point) =
      (‖point‖ ^ 2) •
        (bilinear (diskBasis 0) (diskBasis 0) + bilinear (diskBasis 1) (diskBasis 1)) := by
  have pointExpansion := congrArg₂ (fun first second => bilinear first second)
    (disk_basis_decomposition point) (disk_basis_decomposition point)
  have turnExpansion := congrArg₂ (fun first second => bilinear first second)
    (disk_quarterTurn_decomposition point) (disk_quarterTurn_decomposition point)
  rw [pointExpansion, turnExpansion, bilinear_coordinate_expansion,
    bilinear_coordinate_expansion, disk_norm_sq]
  module

theorem radial_differential_equation
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (field : Plane → Target) (radius : ℝ)
    (smooth : ContDiffOn ℝ ∞ field (Metric.ball (0 : Plane) radius))
    (radial : ∀ angle point, point ∈ Metric.ball (0 : Plane) radius →
      field (planeRotationAction angle point) = field point)
    (point : Plane) (scale : ℝ) (scaleNonzero : scale ≠ 0)
    (pointIn : scale • point ∈ Metric.ball (0 : Plane) radius) :
    fderiv ℝ field (scale • point) point +
        scale • fderiv ℝ (fderiv ℝ field) (scale • point) point point =
      scale • ((‖point‖ ^ 2) • diskLaplacian field (scale • point)) := by
  let bilinear := fderiv ℝ (fderiv ℝ field) (scale • point)
  have turnScaled : planeQuarterTurn (scale • point) = scale • planeQuarterTurn point :=
    quarterTurnLinear.map_smul scale point
  have turn := radial_hessian_quarterTurn field radius smooth radial (scale • point) pointIn
  have reduced : scale • bilinear (planeQuarterTurn point) (planeQuarterTurn point) =
      fderiv ℝ field (scale • point) point := by
    apply smul_right_injective Target scaleNonzero
    simpa only [turnScaled, map_smul, smul_apply, smul_smul] using turn
  calc
    _ = scale • (bilinear point point +
        bilinear (planeQuarterTurn point) (planeQuarterTurn point)) := by
      rw [← reduced]
      module
    _ = scale • ((‖point‖ ^ 2) • diskLaplacian field (scale • point)) := by
      rw [bilinear_radial_trace]
      simp [bilinear, diskLaplacian, Fin.sum_univ_two]

theorem diskLaplacian_continuousOn
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (field : Plane → Target) (radius : ℝ)
    (smooth : ContDiffOn ℝ ∞ field (Metric.ball (0 : Plane) radius)) :
    ContinuousOn (diskLaplacian field) (Metric.ball 0 radius) := by
  have firstSmooth : ContDiffOn ℝ ∞ (fderiv ℝ field) (Metric.ball 0 radius) :=
    smooth.fderiv_of_isOpen Metric.isOpen_ball (by simp)
  have secondSmooth : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ field)) (Metric.ball 0 radius) :=
    firstSmooth.fderiv_of_isOpen Metric.isOpen_ball (by simp)
  have identity : diskLaplacian field = fun point =>
      fderiv ℝ (fderiv ℝ field) point (diskBasis 0) (diskBasis 0) +
      fderiv ℝ (fderiv ℝ field) point (diskBasis 1) (diskBasis 1) := by
    funext point
    simp [diskLaplacian, Fin.sum_univ_two]
  rw [identity]
  exact ((secondSmooth.continuousOn.clm_apply continuousOn_const).clm_apply continuousOn_const).add
    ((secondSmooth.continuousOn.clm_apply continuousOn_const).clm_apply continuousOn_const)

theorem radialIntegral_laplacian
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    [CompleteSpace Target]
    (field : Plane → Target) (radius : ℝ)
    (smooth : ContDiffOn ℝ ∞ field (Metric.ball (0 : Plane) radius))
    (radial : ∀ angle point, point ∈ Metric.ball (0 : Plane) radius →
      field (planeRotationAction angle point) = field point)
    (point : Plane) (pointIn : point ∈ Metric.ball (0 : Plane) radius) :
    field point - field 0 = (‖point‖ ^ 2) • radialIntegral (diskLaplacian field) point := by
  have firstSmooth : ContDiffOn ℝ ∞ (fderiv ℝ field) (Metric.ball 0 radius) :=
    smooth.fderiv_of_isOpen Metric.isOpen_ball (by simp)
  have pathIn : ∀ scale ∈ Icc (0 : ℝ) 1,
      scale • point ∈ Metric.ball (0 : Plane) radius := by
    intro scale scaleIn
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg scaleIn.1]
    calc
      scale * ‖point‖ ≤ 1 * ‖point‖ := mul_le_mul_of_nonneg_right scaleIn.2 (norm_nonneg point)
      _ < radius := by simpa [Metric.mem_ball, dist_zero_right] using pointIn
  have pathContinuous : Continuous (fun scale : ℝ => scale • point) := by fun_prop
  have pathDerivative (scale : ℝ) : HasDerivAt (fun current : ℝ => current • point) point scale := by
    have derivative : HasDerivAt (fun current : ℝ => current • point) ((1 : ℝ) • point) scale :=
      (hasDerivAt_id scale).smul_const point
    simpa only [one_smul] using derivative
  let value : ℝ → Target := fun scale => field (scale • point)
  let first : ℝ → Target := fun scale => fderiv ℝ field (scale • point) point
  let second : ℝ → Target := fun scale => fderiv ℝ (fderiv ℝ field) (scale • point) point point
  let forcing : ℝ → Target := fun scale => (‖point‖ ^ 2) • diskLaplacian field (scale • point)
  have valueContinuous : ContinuousOn value (Icc 0 1) :=
    smooth.continuousOn.comp pathContinuous.continuousOn pathIn
  have firstContinuous : ContinuousOn first (Icc 0 1) :=
    (firstSmooth.continuousOn.comp pathContinuous.continuousOn pathIn).clm_apply continuousOn_const
  have forcingContinuous : ContinuousOn forcing (Icc 0 1) :=
    ((diskLaplacian_continuousOn field radius smooth).comp pathContinuous.continuousOn pathIn).const_smul _
  have valueDerivative : ∀ scale ∈ Ioo (0 : ℝ) 1, HasDerivAt value (first scale) scale := by
    intro scale scaleIn
    have outer := (smooth.contDiffAt (Metric.isOpen_ball.mem_nhds
      (pathIn scale ⟨scaleIn.1.le, scaleIn.2.le⟩))).differentiableAt (by simp)
    exact outer.hasFDerivAt.comp_hasDerivAt scale (pathDerivative scale)
  have firstDerivative : ∀ scale ∈ Ioo (0 : ℝ) 1, HasDerivAt first (second scale) scale := by
    intro scale scaleIn
    have outer := (firstSmooth.contDiffAt (Metric.isOpen_ball.mem_nhds
      (pathIn scale ⟨scaleIn.1.le, scaleIn.2.le⟩))).differentiableAt (by simp)
    have derivativeMap : HasDerivAt (fun current : ℝ => fderiv ℝ field (current • point))
        (fderiv ℝ (fderiv ℝ field) (scale • point) point) scale :=
      outer.hasFDerivAt.comp_hasDerivAt scale (pathDerivative scale)
    have derivative : HasDerivAt (fun current : ℝ => fderiv ℝ field (current • point) point)
        (fderiv ℝ (fderiv ℝ field) (scale • point) point point +
          fderiv ℝ field (scale • point) 0) scale :=
      derivativeMap.clm_apply (hasDerivAt_const scale point)
    simpa only [map_zero, add_zero] using derivative
  have equation := radial_ode_integral value first second forcing
    valueContinuous firstContinuous forcingContinuous valueDerivative firstDerivative
    (fun scale scaleIn => radial_differential_equation field radius smooth radial
      point scale scaleIn.1.ne' (pathIn scale ⟨scaleIn.1.le, scaleIn.2.le⟩))
  have integralIdentity : (∫ scale in (0 : ℝ)..1, Real.negMulLog scale • forcing scale) =
      (‖point‖ ^ 2) • radialIntegral (diskLaplacian field) point := by
    unfold forcing radialIntegral
    simp_rw [smul_comm (Real.negMulLog _) (‖point‖ ^ 2)]
    exact intervalIntegral.integral_smul _ _
  rw [integralIdentity] at equation
  simpa [value] using equation.symm

theorem radialDivision : RadialDivisionGoal := by
  intro field radius _ smooth radial zero point pointIn
  have identity := radialIntegral_laplacian field radius smooth radial point pointIn
  simpa [zero] using identity

end Grad.NonlinearQuotient
