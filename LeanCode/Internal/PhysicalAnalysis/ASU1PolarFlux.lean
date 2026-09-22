import ANR41CoreGradientIntegral

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.SmoothRobinUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.BoundaryTrace
open Grad.CircularHighRegularity Grad.NonlinearQuotient Grad.PhysicalFamily

/-- Radial flux includes its area factor, so its axis trace is literally zero. -/
def radialFlux (test field : SpatialPlane → ComplexEuclidean 1) (point : ℝ × ℝ) : ℂ :=
  point.1 • inner ℂ (test (polarPlane point))
    (fderiv ℝ field (polarPlane point) (radialDirection point.2))

/-- The normalized tangential flux remains smooth at radius zero. -/
def angularFlux (test field : SpatialPlane → ComplexEuclidean 1) (point : ℝ × ℝ) : ℂ :=
  inner ℂ (test (polarPlane point))
    (fderiv ℝ field (polarPlane point) (planeQuarterTurn (radialDirection point.2)))

def radialFluxDensity (test field : SpatialPlane → ComplexEuclidean 1) (point : ℝ × ℝ) : ℂ :=
  point.1 • (inner ℂ (test (polarPlane point))
    (fderiv ℝ (fderiv ℝ field) (polarPlane point) (radialDirection point.2) (radialDirection point.2)) +
    inner ℂ (fderiv ℝ test (polarPlane point) (radialDirection point.2))
      (fderiv ℝ field (polarPlane point) (radialDirection point.2))) +
  inner ℂ (test (polarPlane point)) (fderiv ℝ field (polarPlane point) (radialDirection point.2))

def angularFluxDensity (test field : SpatialPlane → ComplexEuclidean 1) (point : ℝ × ℝ) : ℂ :=
  point.1 • inner ℂ (test (polarPlane point))
    (fderiv ℝ (fderiv ℝ field) (polarPlane point)
      (planeQuarterTurn (radialDirection point.2)) (planeQuarterTurn (radialDirection point.2))) -
  inner ℂ (test (polarPlane point)) (fderiv ℝ field (polarPlane point) (radialDirection point.2)) +
  point.1 • inner ℂ (fderiv ℝ test (polarPlane point) (planeQuarterTurn (radialDirection point.2)))
    (fderiv ℝ field (polarPlane point) (planeQuarterTurn (radialDirection point.2)))

theorem radialFlux_hasDerivAt (test field : SpatialPlane → ComplexEuclidean 1)
    (testSmooth : ContDiff ℝ ∞ test) (fieldSmooth : ContDiff ℝ ∞ field) (radius angle : ℝ) :
    HasDerivAt (fun current => radialFlux test field (current, angle))
      (radialFluxDensity test field (radius, angle)) radius := by
  have first := (testSmooth.differentiable (by simp) (polarPlane (radius, angle))).hasFDerivAt.comp_hasDerivAt
    radius (polarPlane_radial_derivative radius angle)
  have second := ((contDiff_infty_iff_fderiv.mp fieldSmooth).2.differentiable (by simp)
    (polarPlane (radius, angle))).hasFDerivAt.comp_hasDerivAt radius (polarPlane_radial_derivative radius angle)
  have slope := second.clm_apply (hasDerivAt_const radius (radialDirection angle))
  have pairing := first.inner ℂ slope
  have product := (hasDerivAt_id radius).smul pairing
  simpa only [radialFlux, radialFluxDensity, Function.comp_apply, map_zero, add_zero, one_smul, id_eq, Pi.smul_apply] using! product

theorem angularFlux_hasDerivAt (test field : SpatialPlane → ComplexEuclidean 1)
    (testSmooth : ContDiff ℝ ∞ test) (fieldSmooth : ContDiff ℝ ∞ field) (radius angle : ℝ) :
    HasDerivAt (fun current => angularFlux test field (radius, current))
      (angularFluxDensity test field (radius, angle)) angle := by
  have first := (testSmooth.differentiable (by simp) (polarPlane (radius, angle))).hasFDerivAt.comp_hasDerivAt
    angle (polarPlane_angular_derivative radius angle)
  have second := ((contDiff_infty_iff_fderiv.mp fieldSmooth).2.differentiable (by simp)
    (polarPlane (radius, angle))).hasFDerivAt.comp_hasDerivAt angle (polarPlane_angular_derivative radius angle)
  have turn := quarterTurnCLM.hasFDerivAt.comp_hasDerivAt angle (radialDirection_hasDerivAt angle)
  have slope := second.clm_apply turn
  have pairing := first.inner ℂ slope
  simpa only [angularFlux, angularFluxDensity, Function.comp_apply, quarterTurnCLM_apply,
    quarterTurn_twice, map_neg, map_smul, smul_apply, inner_add_right, inner_neg_right,
    inner_smul_right_eq_smul, inner_smul_left_eq_smul, sub_eq_add_neg] using pairing

private def complexInnerReal : ComplexEuclidean 1 →L[ℝ] ComplexEuclidean 1 →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    ({ toFun := fun first : ComplexEuclidean 1 => (innerSL ℂ first).restrictScalars ℝ
       map_add' := by intro first second; ext value; exact inner_add_left (𝕜 := ℂ) first second value
       map_smul' := by intro scalar first; ext value; exact inner_smul_left_eq_smul first value scalar } :
      ComplexEuclidean 1 →ₗ[ℝ] ComplexEuclidean 1 →L[ℝ] ℂ)
    1 (by
      intro first
      rw [one_mul]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg first)
      intro second
      exact norm_inner_le_norm (𝕜 := ℂ) first second)

/-- The full polar divergence identity has no reciprocal and is valid at the axis. -/
theorem polarFlux_divergence (test field : SpatialPlane → ComplexEuclidean 1) (radius angle : ℝ) :
    radialFluxDensity test field (radius, angle) + angularFluxDensity test field (radius, angle) =
      radius • (cartesianGradientPairing test field (polarPlane (radius, angle)) +
        inner ℂ (test (polarPlane (radius, angle))) (diskLaplacian field (polarPlane (radius, angle)))) := by
  have gradient := bilinear_radial_trace
    (complexInnerReal.bilinearComp (fderiv ℝ test (polarPlane (radius, angle))) (fderiv ℝ field (polarPlane (radius, angle))))
    (radialDirection angle)
  rw [radialDirection_norm, one_pow, one_smul] at gradient
  change inner ℂ (fderiv ℝ test (polarPlane (radius, angle)) (radialDirection angle))
      (fderiv ℝ field (polarPlane (radius, angle)) (radialDirection angle)) +
    inner ℂ (fderiv ℝ test (polarPlane (radius, angle)) (planeQuarterTurn (radialDirection angle)))
      (fderiv ℝ field (polarPlane (radius, angle)) (planeQuarterTurn (radialDirection angle))) =
      cartesianGradientPairing test field (polarPlane (radius, angle)) at gradient
  have hessian := bilinear_radial_trace (fderiv ℝ (fderiv ℝ field) (polarPlane (radius, angle))) (radialDirection angle)
  rw [radialDirection_norm, one_pow, one_smul] at hessian
  have laplacian : fderiv ℝ (fderiv ℝ field) (polarPlane (radius, angle)) (radialDirection angle) (radialDirection angle) +
    fderiv ℝ (fderiv ℝ field) (polarPlane (radius, angle))
      (planeQuarterTurn (radialDirection angle)) (planeQuarterTurn (radialDirection angle)) =
      diskLaplacian field (polarPlane (radius, angle)) := by
    simpa only [diskLaplacian, Fin.sum_univ_two] using hessian
  rw [← gradient, ← laplacian]
  simp only [radialFluxDensity, angularFluxDensity, inner_add_right, smul_add]
  module

end Grad.SmoothRobinUniqueness
