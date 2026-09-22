import AKB2ConjugatedFluxSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set
namespace Grad.AnnularWeightedSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.AnnularJointRegularity Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularOriginalLow
open Grad.AnnularSmoothCore Grad.PhaseAlgebra Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)

/-- The remaining original low balancing factor after exact phase cancellation. -/
def conjugatedLowInverseCurve (index : LowAnnularIndex) : C(ℝ, ℝ) :=
  if index.1 = 0 then
    (lowAmplitude length parameters.gamma index.2)⁻¹ • lowMuInverseCurve lower length positive index.2.val.2
  else 1

def conjugatedLowSection (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    RadialContinuousSection 1 lower :=
  radialSectionScalar lower (conjugatedLowInverseCurve parameters lower length positive index)
    (lowEnergySection lower length positive bounded field index)

theorem conjugatedLowInverseCurve_bound (index : LowAnnularIndex)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |conjugatedLowInverseCurve parameters lower length positive index radius| ≤ 2 := by
  have mu : |(lowMuCurve lower length positive index.2.val.2 radius)⁻¹| ≤ 1 := by
    change |(lowMu length (max lower radius) index.2.val.2)⁻¹| ≤ 1
    rw [max_eq_right inside.1, abs_of_pos (inv_pos.mpr (lowMu_pos length radius index.2.val.2 (positive.trans_le inside.1)))]
    exact inv_le_one_of_one_le₀ (lowMu_inner_one_le radius length (positive.trans_le inside.1) inside.2 index.2.val.2)
  unfold conjugatedLowInverseCurve
  split_ifs
  · change |(lowAmplitude length parameters.gamma index.2)⁻¹ *
      (lowMuCurve lower length positive index.2.val.2 radius)⁻¹| ≤ 2
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul
      (lowAmplitude_inverse_bound length parameters.gamma index.2) mu (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  · change |(1 : ℝ)| ≤ 2
    norm_num

theorem conjugatedLowSection_physical (field : lowEnergyGraph lower length positive)
    (index : LowAnnularIndex) (radius : Icc lower (1 : ℝ)) :
    Real.exp (radialPhase parameters radius.val index.2.val.2) •
      lowPhysicalSection parameters lower length positive bounded field index radius =
      conjugatedLowSection parameters lower length positive bounded field index radius := by
  change Real.exp (radialPhase parameters radius.val index.2.val.2) •
    (lowPhysicalInverseCurve parameters lower length positive index radius.val •
      lowEnergySection lower length positive bounded field index radius) =
    conjugatedLowInverseCurve parameters lower length positive index radius.val •
      lowEnergySection lower length positive bounded field index radius
  rw [smul_smul]
  congr 1
  unfold lowPhysicalInverseCurve conjugatedLowInverseCurve
  split_ifs
  · change Real.exp (radialPhase parameters radius.val index.2.val.2) *
      ((lowAmplitude length parameters.gamma index.2)⁻¹ *
        (Real.exp (-radialPhase parameters radius.val index.2.val.2) *
          (lowMuCurve lower length positive index.2.val.2 radius.val)⁻¹)) =
      (lowAmplitude length parameters.gamma index.2)⁻¹ *
        (lowMuCurve lower length positive index.2.val.2 radius.val)⁻¹
    rw [Real.exp_neg]
    field_simp
  · change Real.exp (radialPhase parameters radius.val index.2.val.2) *
      Real.exp (-radialPhase parameters radius.val index.2.val.2) = 1
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

theorem conjugatedLowSection_bound
    (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) (radius : Icc lower (1 : ℝ)) :
    ‖conjugatedLowSection parameters lower length positive bounded field index radius‖ ≤
      (2 * sourceEndpointConstant lower) *
        (‖field.val 0 index‖ + lowMu length lower index.2.val.2 * ‖field.val 1 index‖) := by
  have representative := (weightedRadialSection_exists 1 lower positive bounded).choose_spec.2
    (lowEnergyRadialGraph lower length positive bounded field index)
  have point := (lowEnergySection lower length positive bounded field index).norm_coe_le_norm radius
  have bound := point.trans (representative.trans (mul_le_mul_of_nonneg_left
    (actualLowMode_H1_bound lower length positive bounded field index) (Real.sqrt_nonneg _)))
  change ‖conjugatedLowInverseCurve parameters lower length positive index radius.val •
    lowEnergySection lower length positive bounded field index radius‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs]
  exact ((mul_le_mul_of_nonneg_right
    (conjugatedLowInverseCurve_bound parameters lower length positive index radius.val radius.property) (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left bound (by norm_num))).trans_eq (by ring)


end Grad.AnnularWeightedSmoothCore
