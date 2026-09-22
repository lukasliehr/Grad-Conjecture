import ASU1PolarFlux

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.SmoothRobinUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.BoundaryTrace
open Grad.CircularHighRegularity Grad.NonlinearQuotient Grad.PhysicalFamily

theorem radialFlux_smooth (test field : SpatialPlane → ComplexEuclidean 1)
    (testSmooth : ContDiff ℝ ∞ test) (fieldSmooth : ContDiff ℝ ∞ field) :
    ContDiff ℝ ∞ (radialFlux test field) := by
  exact contDiff_fst.smul ((testSmooth.comp polarPlane_smooth).inner ℂ
    (((contDiff_infty_iff_fderiv.mp fieldSmooth).2.comp polarPlane_smooth).clm_apply
      (radialDirection_smooth.comp contDiff_snd)))

theorem angularFlux_smooth (test field : SpatialPlane → ComplexEuclidean 1)
    (testSmooth : ContDiff ℝ ∞ test) (fieldSmooth : ContDiff ℝ ∞ field) :
    ContDiff ℝ ∞ (angularFlux test field) := by
  exact (testSmooth.comp polarPlane_smooth).inner ℂ
    (((contDiff_infty_iff_fderiv.mp fieldSmooth).2.comp polarPlane_smooth).clm_apply
      (quarterTurnCLM.contDiff.comp (radialDirection_smooth.comp contDiff_snd)))

theorem radialFluxDensity_continuous (test field : SpatialPlane → ComplexEuclidean 1)
    (testSmooth : ContDiff ℝ ∞ test) (fieldSmooth : ContDiff ℝ ∞ field) :
    Continuous (radialFluxDensity test field) := by
  have t := testSmooth.continuous.comp polarPlane_smooth.continuous
  have dt := (contDiff_infty_iff_fderiv.mp testSmooth).2.continuous.comp polarPlane_smooth.continuous
  have df := (contDiff_infty_iff_fderiv.mp fieldSmooth).2.continuous.comp polarPlane_smooth.continuous
  have ddf := (contDiff_infty_iff_fderiv.mp (contDiff_infty_iff_fderiv.mp fieldSmooth).2).2.continuous.comp
    polarPlane_smooth.continuous
  have e : Continuous (fun point : ℝ × ℝ => radialDirection point.2) :=
    radialDirection_smooth.continuous.comp continuous_snd
  exact (continuous_fst.smul ((t.inner ((ddf.clm_apply e).clm_apply e)).add
    ((dt.clm_apply e).inner (df.clm_apply e)))).add (t.inner (df.clm_apply e))

theorem angularFluxDensity_continuous (test field : SpatialPlane → ComplexEuclidean 1)
    (testSmooth : ContDiff ℝ ∞ test) (fieldSmooth : ContDiff ℝ ∞ field) :
    Continuous (angularFluxDensity test field) := by
  have t := testSmooth.continuous.comp polarPlane_smooth.continuous
  have dt := (contDiff_infty_iff_fderiv.mp testSmooth).2.continuous.comp polarPlane_smooth.continuous
  have df := (contDiff_infty_iff_fderiv.mp fieldSmooth).2.continuous.comp polarPlane_smooth.continuous
  have ddf := (contDiff_infty_iff_fderiv.mp (contDiff_infty_iff_fderiv.mp fieldSmooth).2).2.continuous.comp
    polarPlane_smooth.continuous
  have e : Continuous (fun point : ℝ × ℝ => radialDirection point.2) :=
    radialDirection_smooth.continuous.comp continuous_snd
  have j := quarterTurnCLM.continuous.comp e
  exact ((continuous_fst.smul (t.inner ((ddf.clm_apply j).clm_apply j))).sub
    (t.inner (df.clm_apply e))).add (continuous_fst.smul ((dt.clm_apply j).inner (df.clm_apply j)))

theorem radialFlux_axis (test field : SpatialPlane → ComplexEuclidean 1) (angle : ℝ) :
    radialFlux test field (0, angle) = 0 := by simp [radialFlux]

theorem angularFlux_periodic (test field : SpatialPlane → ComplexEuclidean 1) (radius : ℝ) :
    Function.Periodic (fun angle => angularFlux test field (radius, angle)) (2 * Real.pi) := by
  intro angle
  have polar : polarPlane (radius, angle + 2 * Real.pi) = polarPlane (radius, angle) := by
    rw [polarPlane_eq, radialDirection_periodic, ← polarPlane_eq]
  dsimp only [angularFlux]
  rw [polar, radialDirection_periodic]

theorem radialFlux_integral (test field : SpatialPlane → ComplexEuclidean 1)
    (testSmooth : ContDiff ℝ ∞ test) (fieldSmooth : ContDiff ℝ ∞ field) (angle : ℝ) :
    (∫ radius in Icc (0 : ℝ) 1, radialFluxDensity test field (radius, angle)) =
      radialFlux test field (1, angle) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun radius _ => radialFlux_hasDerivAt test field testSmooth fieldSmooth radius angle)
    (((radialFluxDensity_continuous test field testSmooth fieldSmooth).comp
      (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1)
  exact integral.trans (by rw [radialFlux_axis, sub_zero])

theorem angularFlux_integral (test field : SpatialPlane → ComplexEuclidean 1)
    (testSmooth : ContDiff ℝ ∞ test) (fieldSmooth : ContDiff ℝ ∞ field) (radius : ℝ) :
    (∫ angle in Icc (-Real.pi) Real.pi, angularFluxDensity test field (radius, angle)) = 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun angle _ => angularFlux_hasDerivAt test field testSmooth fieldSmooth radius angle)
    (((angularFluxDensity_continuous test field testSmooth fieldSmooth).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable (-Real.pi) Real.pi)
  have endpoint := angularFlux_periodic test field radius (-Real.pi)
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at endpoint
  exact integral.trans (sub_eq_zero.mpr endpoint)

/-- Genuine radial FTC and angular periodic FTC on the whole disk rectangle. -/
theorem fullDisk_flux_integral (test field : SpatialPlane → ComplexEuclidean 1)
    (testSmooth : ContDiff ℝ ∞ test) (fieldSmooth : ContDiff ℝ ∞ field) :
    (∫ radius in Icc (0 : ℝ) 1, ∫ angle in Icc (-Real.pi) Real.pi,
      radius • (cartesianGradientPairing test field (polarPlane (radius, angle)) +
        inner ℂ (test (polarPlane (radius, angle))) (diskLaplacian field (polarPlane (radius, angle))))) =
      ∫ angle in Icc (-Real.pi) Real.pi, radialFlux test field (1, angle) := by
  have rd := radialFluxDensity_continuous test field testSmooth fieldSmooth
  have ad := angularFluxDensity_continuous test field testSmooth fieldSmooth
  have rectangle : Integrable (radialFluxDensity test field)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact rd.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have integrands (radius : ℝ) :
      (∫ angle in Icc (-Real.pi) Real.pi,
        radius • (cartesianGradientPairing test field (polarPlane (radius, angle)) +
          inner ℂ (test (polarPlane (radius, angle))) (diskLaplacian field (polarPlane (radius, angle))))) =
      ∫ angle in Icc (-Real.pi) Real.pi, radialFluxDensity test field (radius, angle) := by
    have rewrite := integral_congr_ae (μ := volume.restrict (Icc (-Real.pi) Real.pi))
      (Filter.Eventually.of_forall (fun angle => (polarFlux_divergence test field radius angle).symm))
    have ri : IntegrableOn (fun angle : ℝ => radialFluxDensity test field (radius, angle))
        (Icc (-Real.pi) Real.pi) :=
      (rd.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_Icc
    have ai : IntegrableOn (fun angle : ℝ => angularFluxDensity test field (radius, angle))
        (Icc (-Real.pi) Real.pi) :=
      (ad.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_Icc
    rw [integral_add ri ai, angularFlux_integral test field testSmooth fieldSmooth, add_zero] at rewrite
    exact rewrite
  simp_rw [integrands]
  have swap : (∫ radius in Icc (0 : ℝ) 1, ∫ angle in Icc (-Real.pi) Real.pi,
      radialFluxDensity test field (radius, angle)) =
    ∫ angle in Icc (-Real.pi) Real.pi, ∫ radius in Icc (0 : ℝ) 1,
      radialFluxDensity test field (radius, angle) := integral_integral_swap rectangle
  rw [swap]
  apply integral_congr_ae
  filter_upwards [] with angle
  exact radialFlux_integral test field testSmooth fieldSmooth angle

end Grad.SmoothRobinUniqueness
