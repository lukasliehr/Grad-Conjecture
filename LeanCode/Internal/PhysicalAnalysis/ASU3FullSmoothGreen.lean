import ASU2IntegratedFlux

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.SmoothRobinUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.BoundaryTrace
open Grad.CircularHighRegularity Grad.CircularHighWeak Grad.NonlinearQuotient Grad.PhysicalFamily
open Grad.NonlinearDivision Grad.NonlinearRange Grad.Constraints

local instance circlePeriodPositive : Fact (0 < (2 * Real.pi : ℝ)) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

theorem diskLaplacian_continuous (field : SpatialPlane → ComplexEuclidean 1)
    (smooth : ContDiff ℝ ∞ field) : Continuous (diskLaplacian field) := by
  have second := (contDiff_infty_iff_fderiv.mp (contDiff_infty_iff_fderiv.mp smooth).2).2.continuous
  unfold diskLaplacian
  apply continuous_finsetSum
  intro direction _
  exact (second.clm_apply continuous_const).clm_apply continuous_const

private theorem disk_integrable (field : SpatialPlane → ℂ) (continuousField : Continuous field) :
    IntegrableOn field openUnitDisk := by
  have compact : IsCompact closedUnitDisk := by
    rw [closedUnitDisk_eq_closedBall]
    exact isCompact_closedBall _ _
  exact (continuousField.continuousOn.integrableOn_compact compact).mono_set
    (fun point inside => openDiskMembershipClosed point inside)

/-- Full smooth Green formula with literal ordinary disk area and angular measure. -/
theorem smoothGreen_integral (test field : SpatialPlane → ComplexEuclidean 1)
    (testSmooth : ContDiff ℝ ∞ test) (fieldSmooth : ContDiff ℝ ∞ field) :
    (∫ point in openUnitDisk, cartesianGradientPairing test field point +
      inner ℂ (test point) (diskLaplacian field point)) =
      ∫ angle in Icc (-Real.pi) Real.pi, radialFlux test field (1, angle) := by
  have continuousIntegrand := (cartesianGradientPairing_continuous test field testSmooth fieldSmooth).add
    (testSmooth.continuous.inner (diskLaplacian_continuous field fieldSmooth))
  have polar := closedDisk_polar_complex
    (fun point => cartesianGradientPairing test field point + inner ℂ (test point) (diskLaplacian field point))
    continuousIntegrand
  rw [Measure.restrict_congr_set closedUnitDisk_ae_openUnitDisk] at polar
  exact polar.trans (fullDisk_flux_integral test field testSmooth fieldSmooth)

theorem coreBoundary_inner_literal (test field : ClosedJet 1) :
    inner ℂ (coreBoundaryL2 test) (coreBoundaryL2 field) =
      ∫ angle in Icc (-Real.pi) Real.pi,
        inner ℂ (test.value (boundaryDiskPoint (angle : CellCircle)))
          (field.value (boundaryDiskPoint (angle : CellCircle))) := by
  rw [L2.inner_def]
  have literal : (∫ angle : CellCircle, inner ℂ (coreBoundaryL2 test angle) (coreBoundaryL2 field angle)) =
      ∫ angle : CellCircle, inner ℂ (test.value (boundaryDiskPoint angle)) (field.value (boundaryDiskPoint angle)) := by
    apply integral_congr_ae
    filter_upwards [coreBoundaryL2_ae test, coreBoundaryL2_ae field] with angle first second
    rw [first, second]
  rw [literal, ← AddCircle.intervalIntegral_preimage (2 * Real.pi) (-Real.pi)]
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi), ← integral_Icc_eq_integral_Ioc]

theorem radialFlux_boundary (test field : ClosedJet 1) (angle : ℝ) :
    radialFlux (smoothClosedExtension test) (smoothClosedExtension field) (1, angle) =
      inner ℂ (test.value (boundaryDiskPoint (angle : CellCircle)))
        ((eulerJet field).value (boundaryDiskPoint (angle : CellCircle))) := by
  have direction : radialDirection angle = (boundaryDiskPoint (angle : CellCircle)).val :=
    (boundaryCirclePoint_coe angle).symm
  simp only [radialFlux, polarPlane_eq, one_smul, direction]
  rw [smoothClosedExtension_value, ← eulerJet_extension_value]

/-- Full-disk Green identity for arbitrary genuine smooth closed jets; neither test
nor field is required to vanish near the boundary or near the axis. -/
theorem closedJet_Green (test field : ClosedJet 1) :
    inner ℂ (diskGradX (diskCoreInto test)) (diskGradX (diskCoreInto field)) +
      inner ℂ (diskGradY (diskCoreInto test)) (diskGradY (diskCoreInto field)) +
      inner ℂ (closedL2Core test) (closedL2Core (laplacianJet field)) =
      inner ℂ (coreBoundaryL2 test) (coreBoundaryL2 (eulerJet field)) := by
  have coreChange := congrArg (fun core : ClosedJet 1 =>
    inner ℂ (diskGradX (diskCoreInto core)) (diskGradX (diskCoreInto field)) +
      inner ℂ (diskGradY (diskCoreInto core)) (diskGradY (diskCoreInto field)))
    (smoothClosedExtension_restricts test)
  have gradient := coreChange.symm.trans
    (diskCore_gradient_integral (smoothClosedExtension test) (smoothClosedExtension_smooth test) field)
  have laplacian := closedL2_inner_representatives test (laplacianJet field)
    (smoothClosedExtension test) (diskLaplacian (smoothClosedExtension field))
    (fun point => (smoothClosedExtension_value test point).symm)
    (by
      intro point
      have law := laplacianJet_global_literal (smoothClosedExtension field) (smoothClosedExtension_smooth field) point
      exact (congrArg (fun core : ClosedJet 1 => (laplacianJet core).value point)
        (smoothClosedExtension_restricts field)).symm.trans law)
  have gradientIntegrable := disk_integrable _ (cartesianGradientPairing_continuous
    (smoothClosedExtension test) (smoothClosedExtension field) (smoothClosedExtension_smooth test) (smoothClosedExtension_smooth field))
  have laplaceIntegrable := disk_integrable _ ((smoothClosedExtension_smooth test).continuous.inner
    (diskLaplacian_continuous _ (smoothClosedExtension_smooth field)))
  have summed := (congrArg₂ (fun first second : ℂ => first + second) gradient laplacian).trans
    (integral_add gradientIntegrable laplaceIntegrable).symm
  have flux := smoothGreen_integral (smoothClosedExtension test) (smoothClosedExtension field)
    (smoothClosedExtension_smooth test) (smoothClosedExtension_smooth field)
  have boundary : (∫ angle in Icc (-Real.pi) Real.pi,
      radialFlux (smoothClosedExtension test) (smoothClosedExtension field) (1, angle)) =
    ∫ angle in Icc (-Real.pi) Real.pi,
      inner ℂ (test.value (boundaryDiskPoint (angle : CellCircle)))
        ((eulerJet field).value (boundaryDiskPoint (angle : CellCircle))) := by
    apply integral_congr_ae
    filter_upwards [] with angle
    exact radialFlux_boundary test field angle
  exact summed.trans (flux.trans (boundary.trans (coreBoundary_inner_literal test (eulerJet field)).symm))

/-- The same full identity extends continuously to every actual H1 test. -/
theorem completedTest_Green (test : diskGrade) (field : ClosedJet 1) :
    inner ℂ (diskGradX test) (diskGradX (diskCoreInto field)) +
      inner ℂ (diskGradY test) (diskGradY (diskCoreInto field)) +
      inner ℂ (diskBulk test) (closedL2Core (laplacianJet field)) =
      inner ℂ (diskBoundary test) (coreBoundaryL2 (eulerJet field)) := by
  apply isClosed_property diskCoreInto_denseRange (isClosed_eq
    (((diskGradX.continuous.inner continuous_const).add
      (diskGradY.continuous.inner continuous_const)).add (diskBulk.continuous.inner continuous_const))
    (diskBoundary.continuous.inner continuous_const)) _ test
  intro core
  have left := congrArg (fun bulk : DiskL2 1 =>
    inner ℂ (diskGradX (diskCoreInto core)) (diskGradX (diskCoreInto field)) +
      inner ℂ (diskGradY (diskCoreInto core)) (diskGradY (diskCoreInto field)) +
      inner ℂ bulk (closedL2Core (laplacianJet field))) (diskBulk_core core)
  have right := congrArg (fun boundary : BoundaryL2 => inner ℂ boundary (coreBoundaryL2 (eulerJet field)))
    (diskBoundary_core core)
  exact left.trans ((closedJet_Green core field).trans right.symm)

end Grad.SmoothRobinUniqueness
