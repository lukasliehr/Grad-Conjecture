import AEB1OriginalTiltPotential

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Grad.AnnularTiltedReference
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.CircularHighWeak

def annularTiltPhaseRatio (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (mode : HighAnnularMode) : C(ℝ, ℝ) :=
  ⟨fun radius => (annularPhaseSlope parameters mode.val.2 radius - annularTiltExponent / max lower radius) /
      annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius,
    ((annularPhaseSlope_continuous parameters mode.val.2).sub
      (continuous_const.div (continuous_const.max continuous_id)
        (fun _radius => (positive.trans_le (le_max_left _ _)).ne'))).div
      (annularPotentialWeight lower length positive mode.val.1 mode.val.2).continuous
      (fun radius => (annularPotentialWeight_pos lower length positive mode radius).ne')⟩

theorem annularTiltPhaseRatio_bound (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (mode : HighAnnularMode) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |annularTiltPhaseRatio parameters lower length positive mode radius| ≤ Real.sqrt (15 / 16) := by
  have rootPositive := annularPotentialWeight_pos lower length positive mode radius
  have rootSquare := annularPotentialWeight_sq lower length positive mode.val.1 mode.val.2 radius inside.1
  have estimate := annularTiltSlope_dominated parameters length radius mode.val.1 mode.val.2
    lengthPositive (positive.trans_le inside.1) inside.2 mode.property widthHalf widthLength
  change |(annularPhaseSlope parameters mode.val.2 radius - annularTiltExponent / max lower radius) /
    annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius| ≤ _
  rw [max_eq_right inside.1, abs_div, abs_of_pos rootPositive]
  apply (div_le_iff₀ rootPositive).mpr
  have sqrtSquare : Real.sqrt (15 / 16 : ℝ) ^ 2 = 15 / 16 := Real.sq_sqrt (by norm_num)
  have productSquare : (Real.sqrt (15 / 16 : ℝ) *
      annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius) ^ 2 =
      (15 / 16 : ℝ) * annularPotential length radius mode.val.1 mode.val.2 := by
    rw [mul_pow, sqrtSquare, rootSquare]
  nlinarith [abs_nonneg (annularPhaseSlope parameters mode.val.2 radius - annularTiltExponent / radius),
    sq_abs (annularPhaseSlope parameters mode.val.2 radius - annularTiltExponent / radius),
    mul_nonneg (Real.sqrt_nonneg (15 / 16 : ℝ)) rootPositive.le]

def annularTiltPhaseMap (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (mode : HighAnnularMode) : RadialL2 1 lower →L[ℂ] RadialL2 1 lower :=
  scalarRadialMap lower (annularTiltPhaseRatio parameters lower length positive mode) (Real.sqrt (15 / 16))
    (annularTiltPhaseRatio_bound parameters lower length positive lengthPositive widthHalf widthLength mode)

theorem annularTiltPhaseMap_bound (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (mode : HighAnnularMode) (field : RadialL2 1 lower) :
    ‖annularTiltPhaseMap parameters lower length positive lengthPositive widthHalf widthLength mode field‖ ≤
      Real.sqrt (15 / 16 : ℝ) * ‖field‖ :=
  scalarRadialMap_bound _ _ _ _ field

def annularTiltEnergyPhase (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)) :
    annularEnergySpace lower length positive →L[ℂ] AnnularBulk lower :=
  (complexLpTwoMap (annularTiltPhaseMap parameters lower length positive lengthPositive widthHalf widthLength)
    (Real.sqrt (15 / 16)) (Real.sqrt_nonneg _)
    (annularTiltPhaseMap_bound parameters lower length positive lengthPositive widthHalf widthLength)).comp
    (annularEnergyMass lower length positive)

theorem annularTiltEnergyPhase_bound (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (field : annularEnergySpace lower length positive) :
    ‖annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field‖ ≤
      Real.sqrt (15 / 16 : ℝ) * ‖field‖ :=
  (complexLpTwoMap_bound
    (annularTiltPhaseMap parameters lower length positive lengthPositive widthHalf widthLength)
    (Real.sqrt (15 / 16)) (Real.sqrt_nonneg _)
    (annularTiltPhaseMap_bound parameters lower length positive lengthPositive widthHalf widthLength)
    (annularEnergyMass lower length positive field)).trans
    (mul_le_mul_of_nonneg_left (annularEnergyMass_bound lower length positive field) (Real.sqrt_nonneg _))

end Grad.AnnularTiltedReference
