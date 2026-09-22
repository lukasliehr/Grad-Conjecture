import ANR36BoundaryCharacterTests

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.BoundaryTrace
open Grad.NonlinearQuotient Grad.PhysicalFamily

private def gradientInnerReal : ComplexEuclidean 1 →L[ℝ] ComplexEuclidean 1 →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    ({ toFun := fun first : ComplexEuclidean 1 => (innerSL ℂ first).restrictScalars ℝ
       map_add' := by intro first second; ext value; exact inner_add_left (𝕜 := ℂ) first second value
       map_smul' := by
         intro scalar first
         ext value
         exact inner_smul_left_eq_smul first value scalar } :
      ComplexEuclidean 1 →ₗ[ℝ] ComplexEuclidean 1 →L[ℝ] ℂ)
    1 (by
      intro first
      rw [one_mul]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg first)
      intro second
      exact norm_inner_le_norm (𝕜 := ℂ) first second)

/-- The exact Cartesian gradient pairing in polar coordinates, with
the original r² factors and no change of area or angular normalization. -/
theorem polar_gradient_pairing (first second : SpatialPlane → ComplexEuclidean 1)
    (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second) (radius angle : ℝ) :
    radius ^ 2 • (inner ℂ (fderiv ℝ first (polarPlane (radius, angle)) (diskBasis 0))
        (fderiv ℝ second (polarPlane (radius, angle)) (diskBasis 0)) +
      inner ℂ (fderiv ℝ first (polarPlane (radius, angle)) (diskBasis 1))
        (fderiv ℝ second (polarPlane (radius, angle)) (diskBasis 1))) =
      radius ^ 2 • inner ℂ (radialField (first ∘ polarPlane) (radius, angle))
        (radialField (second ∘ polarPlane) (radius, angle)) +
      inner ℂ (angularJet 1 (first ∘ polarPlane) (radius, angle))
        (angularJet 1 (second ∘ polarPlane) (radius, angle)) := by
  let firstDerivative := fderiv ℝ first (polarPlane (radius, angle))
  let secondDerivative := fderiv ℝ second (polarPlane (radius, angle))
  let pairing := gradientInnerReal.bilinearComp firstDerivative secondDerivative
  have trace := bilinear_radial_trace pairing (radialDirection angle)
  rw [radialDirection_norm, one_pow, one_smul] at trace
  change inner ℂ (firstDerivative (radialDirection angle)) (secondDerivative (radialDirection angle)) +
    inner ℂ (firstDerivative (planeQuarterTurn (radialDirection angle)))
      (secondDerivative (planeQuarterTurn (radialDirection angle))) =
    inner ℂ (firstDerivative (diskBasis 0)) (secondDerivative (diskBasis 0)) +
      inner ℂ (firstDerivative (diskBasis 1)) (secondDerivative (diskBasis 1)) at trace
  rw [polar_radial_first first firstSmooth, polar_radial_first second secondSmooth,
    polar_angular_first first firstSmooth, polar_angular_first second secondSmooth]
  change radius ^ 2 • (_ + _) = radius ^ 2 •
    inner ℂ (firstDerivative (radialDirection angle)) (secondDerivative (radialDirection angle)) +
    inner ℂ (firstDerivative (radius • planeQuarterTurn (radialDirection angle)))
      (secondDerivative (radius • planeQuarterTurn (radialDirection angle)))
  rw [map_smul, map_smul, inner_smul_left_eq_smul, inner_smul_right_eq_smul, smul_smul,
    ← pow_two, ← smul_add, trace]

end Grad.CircularHighRegularity
