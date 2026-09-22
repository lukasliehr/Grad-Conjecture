import ANR38CharacterGradientCoefficients
import ANR39BoundaryTestL2Pairing

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.BoundaryTrace
open Grad.NonlinearQuotient

def cartesianGradientPairing (first second : SpatialPlane → ComplexEuclidean 1) (point : SpatialPlane) : ℂ :=
  inner ℂ (fderiv ℝ first point (diskBasis 0)) (fderiv ℝ second point (diskBasis 0)) +
    inner ℂ (fderiv ℝ first point (diskBasis 1)) (fderiv ℝ second point (diskBasis 1))

theorem cartesianGradientPairing_continuous (first second : SpatialPlane → ComplexEuclidean 1)
    (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second) :
    Continuous (cartesianGradientPairing first second) := by
  have firstContinuous := (contDiff_infty_iff_fderiv.mp firstSmooth).2.continuous
  have secondContinuous := (contDiff_infty_iff_fderiv.mp secondSmooth).2.continuous
  exact ((firstContinuous.clm_apply continuous_const).inner (secondContinuous.clm_apply continuous_const)).add
    ((firstContinuous.clm_apply continuous_const).inner (secondContinuous.clm_apply continuous_const))

theorem polar_gradient_integral_multiplied (first second : SpatialPlane → ComplexEuclidean 1)
    (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second) (radius : ℝ) :
    radius ^ 2 • (∫ angle in Icc (-Real.pi) Real.pi, cartesianGradientPairing first second (polarPlane (radius, angle))) =
      radius ^ 2 • (∫ angle in Icc (-Real.pi) Real.pi,
        inner ℂ (radialField (first ∘ polarPlane) (radius, angle)) (radialField (second ∘ polarPlane) (radius, angle))) +
      ∫ angle in Icc (-Real.pi) Real.pi,
        inner ℂ (angularJet 1 (first ∘ polarPlane) (radius, angle)) (angularJet 1 (second ∘ polarPlane) (radius, angle)) := by
  have radialContinuous : Continuous (fun angle =>
      inner ℂ (radialField (first ∘ polarPlane) (radius, angle)) (radialField (second ∘ polarPlane) (radius, angle))) :=
    (((radialField_smooth _ (firstSmooth.comp polarPlane_smooth)).continuous.comp (continuous_const.prodMk continuous_id)).inner
      ((radialField_smooth _ (secondSmooth.comp polarPlane_smooth)).continuous.comp (continuous_const.prodMk continuous_id)))
  have angularContinuous : Continuous (fun angle =>
      inner ℂ (angularJet 1 (first ∘ polarPlane) (radius, angle)) (angularJet 1 (second ∘ polarPlane) (radius, angle))) :=
    (((angularJet_smooth 1 _ (firstSmooth.comp polarPlane_smooth)).continuous.comp (continuous_const.prodMk continuous_id)).inner
      ((angularJet_smooth 1 _ (secondSmooth.comp polarPlane_smooth)).continuous.comp (continuous_const.prodMk continuous_id)))
  calc
    _ = ∫ angle in Icc (-Real.pi) Real.pi, radius ^ 2 •
        cartesianGradientPairing first second (polarPlane (radius, angle)) := (integral_smul _ _).symm
    _ = ∫ angle in Icc (-Real.pi) Real.pi,
        radius ^ 2 • inner ℂ (radialField (first ∘ polarPlane) (radius, angle)) (radialField (second ∘ polarPlane) (radius, angle)) +
          inner ℂ (angularJet 1 (first ∘ polarPlane) (radius, angle)) (angularJet 1 (second ∘ polarPlane) (radius, angle)) := by
      apply integral_congr_ae
      filter_upwards [] with angle
      exact polar_gradient_pairing first second firstSmooth secondSmooth radius angle
    _ = _ := by
      have radialIntegrable : IntegrableOn (fun angle => radius ^ 2 •
          inner ℂ (radialField (first ∘ polarPlane) (radius, angle)) (radialField (second ∘ polarPlane) (radius, angle)))
          (Icc (-Real.pi) Real.pi) := (radialContinuous.const_smul (radius ^ 2)).continuousOn.integrableOn_Icc
      have angularIntegrable : IntegrableOn (fun angle =>
          inner ℂ (angularJet 1 (first ∘ polarPlane) (radius, angle)) (angularJet 1 (second ∘ polarPlane) (radius, angle)))
          (Icc (-Real.pi) Real.pi) := angularContinuous.continuousOn.integrableOn_Icc
      rw [integral_add radialIntegrable angularIntegrable, integral_smul]

private theorem gradient_radius_cancel (radius period derivative potential : ℝ) (positive : 0 < radius)
    (cartesian first second : ℂ)
    (law : radius ^ 2 • cartesian = radius ^ 2 • (period • (derivative • first)) + period • (potential • second)) :
    radius • cartesian = period • ((radius * derivative) • first + (potential / radius) • second) := by
  apply smul_right_injective ℂ positive.ne'
  dsimp only
  rw [smul_smul, ← pow_two, law]
  rw [smul_comm radius period, smul_add]
  simp only [smul_smul]
  rw [mul_div_cancel₀ _ positive.ne']
  module

theorem character_gradient_angle (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (smooth : ContDiff ℝ ∞ test) (away : (0 : ℝ) ∉ tsupport test)
    (field : ClosedJet 1) (radius : ℝ) (positive : 0 < radius) :
    radius • (∫ angle in Icc (-Real.pi) Real.pi,
      cartesianGradientPairing (radialTestLift mode vector test) (smoothClosedExtension field) (polarPlane (radius, angle))) =
      (2 * Real.pi) • ((radius * deriv test radius) • inner ℂ vector
        (radialCoefficientJet (originalPolarValue field) mode 1 radius) +
      (test radius * (mode : ℝ) ^ 2 / radius) • inner ℂ vector
        (radialCoefficientJet (originalPolarValue field) mode 0 radius)) := by
  have multiplied := polar_gradient_integral_multiplied (radialTestLift mode vector test) (smoothClosedExtension field)
    (radialTestLift_smooth_away_axis mode vector test smooth away) (smoothClosedExtension_smooth field) radius
  have radialLaw := character_radial_gradient_integral mode vector test smooth field radius positive
  have angularLaw := character_angular_gradient_integral mode vector test smooth field radius positive
  dsimp only [originalPolarValue] at radialLaw angularLaw
  rw [radialLaw, angularLaw] at multiplied
  exact gradient_radius_cancel radius (2 * Real.pi) (deriv test radius) (test radius * (mode : ℝ) ^ 2)
    positive _ _ _ multiplied

end Grad.CircularHighRegularity
