import AEB4LiteralBWeightedEnergy
import AAR11SingleModeVariationalFormula
import AAT4TraceLiftCommutation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped Topology Interval BigOperators
namespace Grad.AnnularTiltedReference
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularReconstruction Grad.AnnularGrades Grad.CircularHighWeak
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.CircularHighRegularity

/-- Continuous storage extension of the literal Phi' - alpha/r multiplier. -/
def annularTiltCurve (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (cell : ℤ) : C(ℝ, ℝ) :=
  ⟨fun radius => annularPhaseSlope parameters cell radius - annularTiltExponent / max lower radius,
    (annularPhaseSlope_continuous parameters cell).sub
      (continuous_const.div (continuous_const.max continuous_id)
        (fun _radius => (positive.trans_le (le_max_left _ _)).ne'))⟩

section Coordinates
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem annularTiltEnergyPhase_mode (mode : HighAnnularMode)
    (field : annularEnergySpace lower length positive) :
    annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field mode =
      collarScalar 1 lower (annularTiltCurve parameters lower positive mode.val.2)
        (annularEnergyValue lower length positive field mode) := by
  let mass := annularEnergyMass lower length positive field mode
  change scalarRadialMap lower (annularTiltPhaseRatio parameters lower length positive mode) (Real.sqrt (15 / 16))
      (annularTiltPhaseRatio_bound parameters lower length positive lengthPositive widthHalf widthLength mode) mass =
    collarScalar 1 lower (annularTiltCurve parameters lower positive mode.val.2)
      (scalarRadialMap lower (annularValueMassRatio lower length positive mode) (1 / 3)
        (annularValueMassRatio_bound lower length positive mode) mass)
  apply Lp.ext
  filter_upwards [scalarRadialMap_ae lower (annularTiltPhaseRatio parameters lower length positive mode) (Real.sqrt (15 / 16))
      (annularTiltPhaseRatio_bound parameters lower length positive lengthPositive widthHalf widthLength mode) mass,
    collarScalar_ae 1 lower (annularTiltCurve parameters lower positive mode.val.2)
      (scalarRadialMap lower (annularValueMassRatio lower length positive mode) (1 / 3)
        (annularValueMassRatio_bound lower length positive mode) mass),
    scalarRadialMap_ae lower (annularValueMassRatio lower length positive mode) (1 / 3)
      (annularValueMassRatio_bound lower length positive mode) mass] with radius phase scalar value
  rw [phase, scalar, value]
  change ((annularPhaseSlope parameters mode.val.2 radius - annularTiltExponent / max lower radius) /
    annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius) • mass radius =
    (annularPhaseSlope parameters mode.val.2 radius - annularTiltExponent / max lower radius) •
      ((annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius)⁻¹ • mass radius)
  rw [div_eq_mul_inv, mul_smul]

theorem annularTiltEnergyPhase_core_mode (core : HighAnnularMode →₀ complexSmoothRadialCore 1)
    (mode : HighAnnularMode) :
    annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength
        (annularEnergyCoreInto lower length positive core) mode =
      weightedCurveComplex 1 lower (continuousCurveWeight 1
        (annularTiltCurve parameters lower positive mode.val.2) (core mode).val.1) := by
  rw [annularTiltEnergyPhase_mode, annularEnergyValue_core_mode, collarScalar_weightedCurve]

theorem annularTiltEnergyPhase_bCore_mode (core : HighAnnularMode →₀ complexSmoothRadialCore 1)
    (mode : HighAnnularMode) :
    annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength
        (bEnergyCore lower length positive core) mode =
      (bEnergyWeight mode : ℂ) • weightedCurveComplex 1 lower (continuousCurveWeight 1
        (annularTiltCurve parameters lower positive mode.val.2) (core mode).val.1) := by
  unfold bEnergyCore
  rw [LinearMap.comp_apply, annularTiltEnergyPhase_core_mode, finiteRealDiagonal_apply]
  change weightedCurveComplex 1 lower (continuousCurveWeight 1
    (annularTiltCurve parameters lower positive mode.val.2) ((bEnergyWeight mode : ℂ) • (core mode).val.1)) = _
  rw [map_smul, map_smul]

theorem annularTiltEnergyPhase_bCore_norm_sq (collar : lower ≤ 1)
    (core : HighAnnularMode →₀ complexSmoothRadialCore 1) :
    ‖annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength
      (bEnergyCore lower length positive core)‖ ^ 2 =
      ∑' mode : HighAnnularMode, (highMultiplier mode.val.1)⁻¹ *
        ∫ radius in lower..1, radius *
          (annularPhaseSlope parameters mode.val.2 radius - annularTiltExponent / radius) ^ 2 *
          ‖(core mode).val.1 radius‖ ^ 2 := by
  have formula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    (annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength
      (bEnergyCore lower length positive core))
  norm_num at formula
  rw [formula]
  apply tsum_congr
  intro mode
  rw [annularTiltEnergyPhase_bCore_mode, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs, bEnergyWeight_square]
  congr 1
  let curve := continuousCurveWeight 1 (annularTiltCurve parameters lower positive mode.val.2) (core mode).val.1
  change ‖radialToLp lower curve curve.continuous‖ ^ 2 = _
  rw [radialToLp_norm_sq lower positive.le collar]
  apply intervalIntegral.integral_congr
  intro radius inside
  have inside' : lower ≤ radius := (min_eq_left collar).symm.le.trans inside.1
  change radius * ‖(annularPhaseSlope parameters mode.val.2 radius - annularTiltExponent / max lower radius) •
    (core mode).val.1 radius‖ ^ 2 = _
  rw [max_eq_right inside', norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

end Coordinates
end Grad.AnnularTiltedReference
