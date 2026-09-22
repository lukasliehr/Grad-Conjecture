import AIY4SharedDataSingleNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularStrongData
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularCurrentEnergy
open Grad.AnnularCurrentSource Grad.AnnularHighTilt

variable (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)

/-- Inverse of the BF4 bulk tilt.  The physical phase stays unchanged. -/
def divisionHighUnweight : DivisionRow 1 lower →L[ℂ] DivisionRow 1 lower :=
  complexLpTwoMap
    (fun _ => scalarRadialMap lower
      (highPowerCurve lower highTiltExponent positive) 1
      (highPositivePower_bound lower positive bounded))
    1 zero_le_one (fun _ field => scalarRadialMap_bound lower
      (highPowerCurve lower highTiltExponent positive) 1
      (highPositivePower_bound lower positive bounded) field)

theorem divisionHighUnweight_bound (field : DivisionRow 1 lower) :
    ‖divisionHighUnweight lower positive bounded field‖ ≤ ‖field‖ := by
  simpa only [divisionHighUnweight, one_mul] using complexLpTwoMap_bound
    (fun _ : ℤ × ℤ => scalarRadialMap lower
      (highPowerCurve lower highTiltExponent positive) 1
      (highPositivePower_bound lower positive bounded))
    1 zero_le_one (fun _ field => scalarRadialMap_bound lower
      (highPowerCurve lower highTiltExponent positive) 1
      (highPositivePower_bound lower positive bounded) field) field

theorem divisionHighWeight_bound (field : DivisionRow 1 lower) :
    ‖divisionHighWeight lower positive bounded field‖ ≤
      lower ^ (-highTiltExponent) * ‖field‖ := by
  exact complexLpTwoMap_bound
    (fun _ : ℤ × ℤ => scalarRadialMap lower
      (highPowerCurve lower (-highTiltExponent) positive)
      (lower ^ (-highTiltExponent))
      (highNegativePower_bound lower positive bounded))
    (lower ^ (-highTiltExponent)) (Real.rpow_pos_of_pos positive _).le
    (fun _ field => scalarRadialMap_bound lower
      (highPowerCurve lower (-highTiltExponent) positive)
      (lower ^ (-highTiltExponent))
      (highNegativePower_bound lower positive bounded) field) field

private theorem scalarRadial_inverse (first second : C(ℝ, ℝ))
    (firstBound secondBound : ℝ)
    (firstLaw : ∀ r ∈ Icc lower 1, |first r| ≤ firstBound)
    (secondLaw : ∀ r ∈ Icc lower 1, |second r| ≤ secondBound)
    (inverse : ∀ r, first r * second r = 1) (field : RadialL2 1 lower) :
    scalarRadialMap lower first firstBound firstLaw
      (scalarRadialMap lower second secondBound secondLaw field) = field := by
  apply Lp.ext
  filter_upwards [scalarRadialMap_ae lower first firstBound firstLaw
      (scalarRadialMap lower second secondBound secondLaw field),
    scalarRadialMap_ae lower second secondBound secondLaw field] with radius outer inner
  rw [outer, inner, smul_smul, inverse, one_smul]

theorem divisionHighWeight_unweight (field : DivisionRow 1 lower) :
    divisionHighWeight lower positive bounded
      (divisionHighUnweight lower positive bounded field) = field := by
  apply lp.ext
  funext mode
  apply scalarRadial_inverse lower
    (highPowerCurve lower (-highTiltExponent) positive)
    (highPowerCurve lower highTiltExponent positive)
    (lower ^ (-highTiltExponent)) 1
    (highNegativePower_bound lower positive bounded)
    (highPositivePower_bound lower positive bounded)
  exact highPowerCurve_inverse lower highTiltExponent positive

theorem divisionHighUnweight_weight (field : DivisionRow 1 lower) :
    divisionHighUnweight lower positive bounded
      (divisionHighWeight lower positive bounded field) = field := by
  apply lp.ext
  funext mode
  apply scalarRadial_inverse lower
    (highPowerCurve lower highTiltExponent positive)
    (highPowerCurve lower (-highTiltExponent) positive)
    1 (lower ^ (-highTiltExponent))
    (highPositivePower_bound lower positive bounded)
    (highNegativePower_bound lower positive bounded)
  intro radius
  rw [mul_comm]
  exact highPowerCurve_inverse lower highTiltExponent positive radius

/-- Fixed-collar isomorphism of the genuine original bulk rows; both bounds
keep the exact BF5 cost `lower^(-9/4)` and no extra angular order. -/
def originalBulkWeightEquivalence : DivisionRow 1 lower ≃L[ℂ] DivisionRow 1 lower where
  toLinearEquiv :=
    { (divisionHighWeight lower positive bounded).toLinearMap with
      invFun := divisionHighUnweight lower positive bounded
      left_inv := divisionHighUnweight_weight lower positive bounded
      right_inv := divisionHighWeight_unweight lower positive bounded }
  continuous_toFun := (divisionHighWeight lower positive bounded).continuous
  continuous_invFun := (divisionHighUnweight lower positive bounded).continuous

theorem originalBulkWeightEquivalence_bound (field : DivisionRow 1 lower) :
    ‖originalBulkWeightEquivalence lower positive bounded field‖ ≤
      lower ^ (-9 / 4 : ℝ) * ‖field‖ := by
  change ‖divisionHighWeight lower positive bounded field‖ ≤ lower ^ (-9 / 4 : ℝ) * ‖field‖
  simpa only [highTiltExponent, neg_div] using divisionHighWeight_bound lower positive bounded field

theorem originalBulkWeightEquivalence_inverse_bound (field : DivisionRow 1 lower) :
    ‖(originalBulkWeightEquivalence lower positive bounded).symm field‖ ≤ ‖field‖ :=
  divisionHighUnweight_bound lower positive bounded field

/-- The original unweighted angular derivative is the derivative of the
same unweighted g; the fixed radial weight commutes with the actual `i m`. -/
theorem divisionHighUnweight_angular (g rg : DivisionRow 1 lower)
    (relation : ∀ mode : ℤ × ℤ, rg mode = (Complex.I * (mode.1 : ℂ)) • g mode) :
    ∀ mode : ℤ × ℤ,
      divisionHighUnweight lower positive bounded rg mode =
        (Complex.I * (mode.1 : ℂ)) • divisionHighUnweight lower positive bounded g mode := by
  intro mode
  change scalarRadialMap lower (highPowerCurve lower highTiltExponent positive) 1
      (highPositivePower_bound lower positive bounded) (rg mode) = _
  rw [relation, map_smul]
  rfl

end Grad.AnnularStrongData
