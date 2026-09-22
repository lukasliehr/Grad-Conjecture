import DivisionInterface

noncomputable section

open Set MeasureTheory
open scoped ContDiff Interval Topology

namespace Grad.NonlinearDivision

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearRadial Grad.NonlinearQuotientBounds Grad.PhysicalFamily
open Grad.NonlinearQuotient (radialIntegral diskLaplacian radialIntegral_laplacian integral_radialKernel)

theorem laplacianJet_value {dimension : ℕ} (field : ClosedJet dimension) :
    (laplacianJet field).value = laplacianCoefficient field := by
  unfold laplacianJet
  rw [closedJet_value_add, partialJet_twice, partialJet_twice]
  rfl

/-- The accepted closed-jet Laplacian coefficient is the Cartesian Laplacian
of the accepted smooth extension, at every closed point. -/
theorem laplacianCoefficient_extension {dimension : ℕ} (field : ClosedJet dimension)
    (point : ClosedDisk) :
    laplacianCoefficient field point = diskLaplacian (smoothClosedExtension field) point.val := by
  have identity := laplacianCoefficient_global (smoothClosedExtension field)
    (smoothClosedExtension_smooth field) point
  rw [smoothClosedExtension_restricts] at identity
  exact identity

/-- The accepted radial integral of the Laplacian jet only samples the
segment inside the closed disk, where it is the literal O8 integral of the
Cartesian Laplacian of the smooth extension. -/
theorem integralCoefficient_laplacianJet {dimension : ℕ} (field : ClosedJet dimension)
    (point : ClosedDisk) :
    integralCoefficient (laplacianJet field) point =
      radialIntegral (diskLaplacian (smoothClosedExtension field)) point.val := by
  unfold integralCoefficient radialIntegral
  apply intervalIntegral.integral_congr
  intro scale scaleIn
  have unitScale : scale ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using scaleIn
  apply congrArg (fun value : ComplexEuclidean dimension => Real.negMulLog scale • value)
  let contracted := dilationPoint scale unitScale.1 unitScale.2 point
  change smoothClosedExtension (laplacianJet field) contracted.val =
    diskLaplacian (smoothClosedExtension field) contracted.val
  rw [smoothClosedExtension_value, laplacianJet_value, laplacianCoefficient_extension]

theorem integralCoefficient_eq_intervalValue {dimension : ℕ} (field : ClosedJet dimension)
    (point : ClosedDisk) :
    integralCoefficient field point = radialIntervalValue 0 1 field point.val :=
  (radialIntervalJet_full_value field point).symm

/-- Rotational invariance on the closed disk transfers to the smooth
extension on the open unit disk: both sampled points lie in the disk. -/
theorem extension_rotation {dimension : ℕ} {field : ClosedJet dimension}
    (radial : IsRotationInvariant field) (angle : ℝ) (point : SpatialPlane)
    (pointIn : point ∈ Metric.ball (0 : SpatialPlane) 1) :
    smoothClosedExtension field (planeRotationAction angle point) =
      smoothClosedExtension field point := by
  have closed : point ∈ closedUnitDisk := (mem_ball_zero_iff.mp pointIn).le
  let closedPoint : ClosedDisk := ⟨point, closed⟩
  change smoothClosedExtension field (rotatedPoint angle closedPoint).val =
    smoothClosedExtension field closedPoint.val
  rw [smoothClosedExtension_value, smoothClosedExtension_value]
  exact radial angle closedPoint

theorem extension_origin {dimension : ℕ} {field : ClosedJet dimension}
    (origin : field.value closedOrigin = 0) :
    smoothClosedExtension field 0 = 0 :=
  (smoothClosedExtension_value field closedOrigin).trans origin

/-- O11 on the open unit disk, from the accepted smooth radial identity
applied to the smooth extension with radius one. -/
theorem open_identity {dimension : ℕ} {field : ClosedJet dimension}
    (radial : IsRotationInvariant field) (origin : field.value closedOrigin = 0)
    (point : SpatialPlane) (pointIn : point ∈ Metric.ball (0 : SpatialPlane) 1) :
    smoothClosedExtension field point =
      ‖point‖ ^ 2 • radialIntervalValue 0 1 (laplacianJet field) point := by
  have identity := radialIntegral_laplacian (smoothClosedExtension field) 1
    (smoothClosedExtension_smooth field).contDiffOn
    (fun angle source sourceIn => extension_rotation radial angle source sourceIn) point pointIn
  rw [extension_origin origin, sub_zero] at identity
  rw [identity]
  congr 1
  have closed : point ∈ closedUnitDisk := (mem_ball_zero_iff.mp pointIn).le
  exact (integralCoefficient_laplacianJet field ⟨point, closed⟩).symm.trans
    (integralCoefficient_eq_intervalValue (laplacianJet field) ⟨point, closed⟩)

/-- O11 on the closed disk, boundary included: both sides are continuous on
the plane and agree on the open disk, whose closure is the closed disk. -/
theorem closed_identity {dimension : ℕ} {field : ClosedJet dimension}
    (radial : IsRotationInvariant field) (origin : field.value closedOrigin = 0)
    (point : ClosedDisk) :
    field.value point = ‖point.val‖ ^ 2 • integralCoefficient (laplacianJet field) point := by
  have leftContinuous : Continuous (smoothClosedExtension field) :=
    (smoothClosedExtension_smooth field).continuous
  have rightContinuous : Continuous (fun source : SpatialPlane =>
      ‖source‖ ^ 2 • radialIntervalValue 0 1 (laplacianJet field) source) :=
    (continuous_norm.pow 2).smul (radialIntervalValue_smooth 0 1 (laplacianJet field)).continuous
  have openAgreement : EqOn (smoothClosedExtension field)
      (fun source : SpatialPlane => ‖source‖ ^ 2 • radialIntervalValue 0 1 (laplacianJet field) source)
      (Metric.ball (0 : SpatialPlane) 1) :=
    fun source sourceIn => open_identity radial origin source sourceIn
  have closedAgreement := openAgreement.closure leftContinuous rightContinuous
  rw [closure_ball (0 : SpatialPlane) one_ne_zero] at closedAgreement
  have equality := closedAgreement (mem_closedBall_zero_iff.mpr point.property)
  change smoothClosedExtension field point.val =
    ‖point.val‖ ^ 2 • radialIntervalValue 0 1 (laplacianJet field) point.val at equality
  rw [smoothClosedExtension_value, ← integralCoefficient_eq_intervalValue] at equality
  exact equality

/-- O12 axis value of the accepted radial integral: the kernel integrates to
one quarter and the integrand is constant on the axis. -/
theorem integralCoefficient_origin {dimension : ℕ} (field : ClosedJet dimension) :
    integralCoefficient field closedOrigin = (1 / 4 : ℝ) • field.value closedOrigin := by
  unfold integralCoefficient radialIntegral
  simp only [closedOrigin_val, smul_zero]
  rw [intervalIntegral.integral_smul_const, integral_radialKernel]
  exact congrArg (fun value => (1 / 4 : ℝ) • value) (smoothClosedExtension_value field closedOrigin)

theorem axis_value {dimension : ℕ} (field : ClosedJet dimension) :
    integralCoefficient (laplacianJet field) closedOrigin =
      (1 / 4 : ℝ) • laplacianCoefficient field closedOrigin := by
  rw [integralCoefficient_origin, laplacianJet_value]

/-- FA-nonlinear-radial-division: O11 and O12 on the accepted carrier. -/
theorem actualRadialDivision : RadialDivisionGoal :=
  fun _ field radial origin => ⟨closed_identity radial origin, axis_value field⟩

end Grad.NonlinearDivision
