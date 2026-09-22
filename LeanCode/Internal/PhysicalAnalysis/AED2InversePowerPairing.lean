import AED1CompletedEnergyPairing
import ADZ9CompletedCoordinateAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped BigOperators
namespace Grad.AnnularTiltedReference
open Grad.ClosedJets Grad.AnnularVariational Grad.AnnularReconstruction Grad.SourceCollarDivision
open Grad.CartesianState Grad.CircularHighRegularity Grad.AnnularHighTilt Grad.AnnularFluxTrace

/-- The exact radial logarithmic derivative, including negative fractional powers. -/
theorem highPowerSlope_logarithmic (lower power : ℝ) (positive : 0 < lower)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    highPowerSlopeCurve lower power positive radius =
      highPowerCurve lower power positive radius * (power / max lower radius) := by
  rw [highPowerSlopeCurve_physical lower power positive radius inside,
    highPowerCurve_physical lower power positive radius inside, max_eq_right inside.1,
    Real.rpow_sub_one (positive.trans_le inside.1).ne']
  ring

theorem highBulkUnweight_inner (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (test field : AnnularBulk lower) :
    inner ℂ (highBulkUnweight lower positive bounded test) field =
      inner ℂ test (highBulkUnweight lower positive bounded field) := by
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro mode
  exact scalarRadialMap_inner lower (highPowerCurve lower highTiltExponent positive) 1
    (highPositivePower_bound lower positive bounded) (test mode) (field mode)

theorem highBulkWeight_inner (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (test field : AnnularBulk lower) :
    inner ℂ (highBulkWeight lower positive bounded test) field =
      inner ℂ test (highBulkWeight lower positive bounded field) := by
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro mode
  exact scalarRadialMap_inner lower (highPowerCurve lower (-highTiltExponent) positive)
    (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded) (test mode) (field mode)

/-- Opposite actual powers cancel in the original completed annular pairing. -/
theorem highBulk_inverse_inner (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (test field : AnnularBulk lower) :
    inner ℂ (highBulkWeight lower positive bounded test) (highBulkUnweight lower positive bounded field) =
      inner ℂ test field := by
  rw [highBulkWeight_inner, highBulk_weight_unweight]

/-- A generic bounded radial mass ratio commutes with the actual powers. -/
theorem scalarRadialMap_comm (lower : ℝ) (first second : C(ℝ, ℝ))
    (firstBound secondBound : ℝ)
    (firstLaw : ∀ radius ∈ Icc lower 1, |first radius| ≤ firstBound)
    (secondLaw : ∀ radius ∈ Icc lower 1, |second radius| ≤ secondBound)
    (field : RadialL2 1 lower) :
    scalarRadialMap lower first firstBound firstLaw
      (scalarRadialMap lower second secondBound secondLaw field) =
    scalarRadialMap lower second secondBound secondLaw
      (scalarRadialMap lower first firstBound firstLaw field) := by
  simp only [scalarRadialMap_eq_collarScalar]
  exact collarScalar_comm lower first second field

/-- Exact multiplier identity used for the product derivative and phase cancellation. -/
theorem scalarRadialMap_difference_product (lower : ℝ) (slope weight first second : C(ℝ, ℝ))
    (slopeBound weightBound firstBound secondBound : ℝ)
    (slopeLaw : ∀ radius ∈ Icc lower 1, |slope radius| ≤ slopeBound)
    (weightLaw : ∀ radius ∈ Icc lower 1, |weight radius| ≤ weightBound)
    (firstLaw : ∀ radius ∈ Icc lower 1, |first radius| ≤ firstBound)
    (secondLaw : ∀ radius ∈ Icc lower 1, |second radius| ≤ secondBound)
    (coefficient : ∀ radius ∈ Icc lower 1, slope radius = weight radius * (first radius - second radius))
    (field : RadialL2 1 lower) :
    scalarRadialMap lower slope slopeBound slopeLaw field =
      scalarRadialMap lower weight weightBound weightLaw
        (scalarRadialMap lower first firstBound firstLaw field -
          scalarRadialMap lower second secondBound secondLaw field) := by
  let left := scalarRadialMap lower first firstBound firstLaw field
  let right := scalarRadialMap lower second secondBound secondLaw field
  apply Lp.ext
  filter_upwards [scalarRadialMap_ae lower slope slopeBound slopeLaw field,
    scalarRadialMap_ae lower weight weightBound weightLaw (left - right),
    scalarRadialMap_ae lower first firstBound firstLaw field,
    scalarRadialMap_ae lower second secondBound secondLaw field,
    Lp.coeFn_sub left right, ae_restrict_mem measurableSet_Icc]
    with radius slopeValue weightValue firstValue secondValue subtraction inside
  change left radius = _ at firstValue
  change right radius = _ at secondValue
  rw [slopeValue, weightValue, subtraction, Pi.sub_apply, firstValue, secondValue,
    coefficient radius inside, mul_smul, sub_smul]

end Grad.AnnularTiltedReference
