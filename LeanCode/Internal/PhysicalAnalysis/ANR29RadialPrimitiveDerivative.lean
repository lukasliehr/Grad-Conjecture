import ANR28ActualRadialFlux
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.WeightedTrace

theorem radialInterval_integral_congr (dimension : ℕ) (lower : ℝ)
    (first second : ℝ → ComplexEuclidean dimension)
    (same : first =ᵐ[volume.restrict (Icc lower 1)] second) (radius : Icc lower (1 : ℝ)) :
    (∫ point in lower..radius.val, first point) = ∫ point in lower..radius.val, second point := by
  rw [intervalIntegral.integral_of_le radius.property.1, intervalIntegral.integral_of_le radius.property.1,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
  exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc le_rfl radius.property.2) same)

/-- The literal primitive formula upgrades an a.e. continuous derivative
to the genuine derivative on the closed collar, including both endpoints. -/
theorem radialSection_hasDerivWithinAt (dimension : ℕ) (lower : ℝ) (bounded : lower ≤ 1)
    (representative : RadialContinuousSection dimension lower)
    (derivative : CollarL2 (ComplexEuclidean dimension) lower)
    (continuousDerivative : C(ℝ, ComplexEuclidean dimension))
    (same : derivative =ᵐ[volume.restrict (Icc lower 1)] continuousDerivative)
    (primitive : ∀ radius : Icc lower (1 : ℝ),
      representative radius = representative ⟨lower, le_rfl, bounded⟩ +
        ∫ point in lower..radius.val, derivative point)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (radialSectionExtension dimension lower bounded representative)
      (continuousDerivative radius) (Icc lower 1) radius := by
  let anchor := representative ⟨lower, le_rfl, bounded⟩
  let extension : ℝ → ComplexEuclidean dimension := fun point => anchor + ∫ value in lower..point, continuousDerivative value
  have equality (point : ℝ) (membership : point ∈ Icc lower 1) :
      radialSectionExtension dimension lower bounded representative point = extension point := by
    change representative (radialClamp lower bounded point) = _
    rw [radialClamp_eq lower bounded point membership, primitive]
    exact congrArg (fun value : ComplexEuclidean dimension => anchor + value)
      (radialInterval_integral_congr dimension lower derivative continuousDerivative same ⟨point, membership⟩)
  have differentiated : HasDerivAt extension (continuousDerivative radius) radius :=
    (intervalIntegral.integral_hasDerivAt_right
      (continuousDerivative.continuous.intervalIntegrable lower radius)
      continuousDerivative.continuous.stronglyMeasurable.stronglyMeasurableAtFilter
      continuousDerivative.continuous.continuousAt).const_add anchor
  exact differentiated.hasDerivWithinAt.congr equality (equality radius inside)

theorem radialOrdinary_toLp (dimension : ℕ) (lower : ℝ) (positive : 0 < lower)
    (field : C(ℝ, ComplexEuclidean dimension)) :
    radialOrdinary dimension lower positive (radialToLp lower field field.continuous) =
      collarContinuousL2 (ComplexEuclidean dimension) lower field := by
  apply Lp.ext
  filter_upwards [radialOrdinary_ae dimension lower positive (radialToLp lower field field.continuous),
    radialToLp_ae lower field field.continuous,
    (collarContinuous_memLp (ComplexEuclidean dimension) lower field).coeFn_toLp,
    ae_restrict_mem measurableSet_Icc] with radius decoded stored ordinary inside
  change collarContinuousL2 (ComplexEuclidean dimension) lower field radius = _ at ordinary
  rw [decoded, stored, ordinary, smul_smul, reciprocalRadialWeight, max_eq_right inside.1,
    one_div, inv_mul_cancel₀ (Real.sqrt_pos.2 (positive.trans_le inside.1)).ne', one_smul]

end Grad.CircularHighRegularity
