import AIY7OriginalLowIncomingFactors

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularStrongData
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.AnnularVariational Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularCrossMaps

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length)

def originalLowIncomingWeightMap : LowEnergyBoundary →L[ℂ] LowEnergyBoundary :=
  complexLpTwoMap
    (fun index => (originalLowIncomingWeight parameters lower length index : ℂ) •
      ContinuousLinearMap.id ℂ (ComplexEuclidean 1))
    (originalLowIncomingConstant parameters length * lower ^ (-9 / 4 : ℝ))
    (by have := lowOuterFrequencyConstant_two_le length lengthPositive
        have : 1 ≤ lowBalanceConstant length parameters.gamma := le_max_left _ _
        unfold originalLowIncomingConstant
        positivity)
    (fun index field => by
      change ‖(originalLowIncomingWeight parameters lower length index : ℂ) • field‖ ≤ _
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (originalLowIncomingWeight_bound parameters lower length positive bounded lengthPositive index)
        (norm_nonneg field))

def originalLowIncomingUnweightMap : LowEnergyBoundary →L[ℂ] LowEnergyBoundary :=
  complexLpTwoMap
    (fun index => (originalLowIncomingUnweight parameters lower length index : ℂ) •
      ContinuousLinearMap.id ℂ (ComplexEuclidean 1))
    (2 * lowOuterFrequencyConstant length)
    (by have := lowOuterFrequencyConstant_two_le length lengthPositive; positivity)
    (fun index field => by
      change ‖(originalLowIncomingUnweight parameters lower length index : ℂ) • field‖ ≤ _
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (originalLowIncomingUnweight_bound parameters lower length positive bounded lengthPositive index)
        (norm_nonneg field))

theorem originalLowIncomingWeightMap_bound (field : LowEnergyBoundary) :
    ‖originalLowIncomingWeightMap parameters lower length positive bounded lengthPositive field‖ ≤
      (originalLowIncomingConstant parameters length * lower ^ (-9 / 4 : ℝ)) * ‖field‖ := by
  apply complexLpTwoMap_bound

theorem originalLowIncomingUnweightMap_bound (field : LowEnergyBoundary) :
    ‖originalLowIncomingUnweightMap parameters lower length positive bounded lengthPositive field‖ ≤
      (2 * lowOuterFrequencyConstant length) * ‖field‖ := by
  apply complexLpTwoMap_bound

theorem originalLowIncomingWeightMap_inverse (field : LowEnergyBoundary) :
    originalLowIncomingWeightMap parameters lower length positive bounded lengthPositive
      (originalLowIncomingUnweightMap parameters lower length positive bounded lengthPositive field) = field ∧
    originalLowIncomingUnweightMap parameters lower length positive bounded lengthPositive
      (originalLowIncomingWeightMap parameters lower length positive bounded lengthPositive field) = field := by
  constructor
  · apply lp.ext
    funext index
    change (originalLowIncomingWeight parameters lower length index : ℂ) •
      ((originalLowIncomingUnweight parameters lower length index : ℂ) • field index) = field index
    rw [smul_smul, ← Complex.ofReal_mul,
      originalLowIncomingWeight_inverse parameters lower length positive index, Complex.ofReal_one, one_smul]
  · apply lp.ext
    funext index
    change (originalLowIncomingUnweight parameters lower length index : ℂ) •
      ((originalLowIncomingWeight parameters lower length index : ℂ) • field index) = field index
    rw [smul_smul, ← Complex.ofReal_mul, mul_comm (originalLowIncomingUnweight _ _ _ _),
      originalLowIncomingWeight_inverse parameters lower length positive index, Complex.ofReal_one, one_smul]

def originalLowIncomingEquivalence : LowEnergyBoundary ≃L[ℂ] LowEnergyBoundary where
  toLinearEquiv :=
    { (originalLowIncomingWeightMap parameters lower length positive bounded lengthPositive).toLinearMap with
      invFun := originalLowIncomingUnweightMap parameters lower length positive bounded lengthPositive
      left_inv := fun field => (originalLowIncomingWeightMap_inverse parameters lower length positive bounded lengthPositive field).2
      right_inv := fun field => (originalLowIncomingWeightMap_inverse parameters lower length positive bounded lengthPositive field).1 }
  continuous_toFun := (originalLowIncomingWeightMap parameters lower length positive bounded lengthPositive).continuous
  continuous_invFun := (originalLowIncomingUnweightMap parameters lower length positive bounded lengthPositive).continuous

/-- The original low incoming coordinates are exactly the positive-half
scalar datum and the negative-half angular flux datum. -/
def originalLowIncomingPhysical (field : LowEnergyBoundary) (index : LowAnnularIndex) : ComplexEuclidean 1 :=
  (Real.exp (Grad.PhaseAlgebra.radialPhase parameters lower index.2.val.2) *
    if index.1 = 0 then Real.sqrt (lowIncomingNu index.2) else (Real.sqrt (lowIncomingNu index.2))⁻¹)⁻¹ • field index

theorem originalLowIncomingPhysical_normalization (field : LowEnergyBoundary) (index : LowAnnularIndex) :
    (Real.exp (Grad.PhaseAlgebra.radialPhase parameters lower index.2.val.2) *
      if index.1 = 0 then Real.sqrt (lowIncomingNu index.2) else (Real.sqrt (lowIncomingNu index.2))⁻¹) •
      originalLowIncomingPhysical parameters lower field index = field index := by
  unfold originalLowIncomingPhysical
  rw [smul_smul, mul_inv_cancel₀, one_smul]
  have := Real.sqrt_pos.mpr (lowIncomingNu_pos index.2)
  split_ifs <;> positivity

/-- Literal BF4 low trace normalization, with exactly BE2's balancing and
BE18's `lower^-7/4 mu^-1/2` and with no additional high tilt. -/
theorem originalLowIncomingWeightMap_physical (field : LowEnergyBoundary) (index : LowAnnularIndex) :
    originalLowIncomingWeightMap parameters lower length positive bounded lengthPositive field index =
      (lower ^ (-(7 / 4 : ℝ)) * (Real.sqrt (lowMu length lower index.2.val.2))⁻¹ *
        lowPhysicalFactor parameters length lower index) •
          originalLowIncomingPhysical parameters lower field index := by
  have nu := (Real.sqrt_pos.mpr (lowIncomingNu_pos index.2)).ne'
  have mu := (Real.sqrt_pos.mpr (lowMu_pos length lower index.2.val.2 positive)).ne'
  have phase := (Real.exp_pos (Grad.PhaseAlgebra.radialPhase parameters lower index.2.val.2)).ne'
  have muSq := Real.sq_sqrt (lowMu_nonneg length lower index.2.val.2)
  change (originalLowIncomingWeight parameters lower length index : ℝ) • field index = _
  unfold originalLowIncomingWeight originalLowIncomingPhysical lowPhysicalFactor
  rw [smul_smul]
  congr 1
  split_ifs
  · field_simp
    rw [muSq]
  · field_simp

end Grad.AnnularStrongData
