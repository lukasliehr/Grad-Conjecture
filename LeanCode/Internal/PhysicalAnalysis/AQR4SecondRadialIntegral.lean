import AQR3SecondDerivativeCurve

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval
namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.AnnularSourceGraph Grad.SourceCollarDivision Grad.SourceBoundaryTrace

theorem secondRadialCurve_energy (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (parameter : ℝ) (value slope forcing : C(ℝ, ComplexEuclidean 1)) :
    ‖radialToLp lower (secondRadialCurve lower positive mode parameter value slope forcing)
      (secondRadialCurve lower positive mode parameter value slope forcing).continuous‖ ^ 2 ≤
      4 * ((lower⁻¹) ^ 2 * ‖radialToLp lower slope slope.continuous‖ ^ 2 +
        ((mode : ℝ) ^ 4 * (lower⁻¹) ^ 4 + parameter ^ 4) * ‖radialToLp lower value value.continuous‖ ^ 2 +
        ‖radialToLp lower forcing forcing.continuous‖ ^ 2) := by
  have valueI := (continuous_id.mul (value.continuous.norm.pow 2)).intervalIntegrable (μ := volume) lower 1
  have slopeI := (continuous_id.mul (slope.continuous.norm.pow 2)).intervalIntegrable (μ := volume) lower 1
  have forcingI := (continuous_id.mul (forcing.continuous.norm.pow 2)).intervalIntegrable (μ := volume) lower 1
  let coefficient := (mode : ℝ) ^ 4 * (lower⁻¹) ^ 4 + parameter ^ 4
  have leftI := (continuous_id.mul
    ((secondRadialCurve lower positive mode parameter value slope forcing).continuous.norm.pow 2)).intervalIntegrable (μ := volume) lower 1
  have rightI := (((slopeI.const_mul ((lower⁻¹) ^ 2)).add (valueI.const_mul coefficient)).add forcingI).const_mul 4
  have bound := intervalIntegral.integral_mono_on bounded leftI rightI (fun radius inside => by
    have pointwise := mul_le_mul_of_nonneg_left
      (secondRadialCurve_pointwise lower positive mode parameter value slope forcing radius)
      (positive.le.trans inside.1)
    exact pointwise.trans_eq (by dsimp only [coefficient, Pi.mul_apply, Pi.pow_apply, id_eq]; ring))
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add ((slopeI.const_mul _).add (valueI.const_mul _)) forcingI,
    intervalIntegral.integral_add (slopeI.const_mul _) (valueI.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at bound
  simpa only [radialToLp_norm_sq lower positive.le bounded, coefficient,
    Pi.mul_apply, Pi.pow_apply, id_eq] using bound

def actualSecondRadialEnergy (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1) (mode : ℤ) : ℝ :=
  ‖radialToLp lower (actualRadialSecond lower positive bounded mode parameter source core)
    (actualRadialSecond lower positive bounded mode parameter source core).continuous‖ ^ 2

theorem actualSecondRadialEnergy_literal (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core)
    (mode : ℤ) (high : mode ∉ lowAngularModes) :
    actualSecondRadialEnergy lower positive bounded parameter source core mode =
      ∫ radius in lower..1, radius *
        ‖derivWithin (derivWithin (actualRadialValue lower positive bounded mode parameter source) (Icc lower 1))
          (Icc lower 1) radius‖ ^ 2 := by
  unfold actualSecondRadialEnergy
  rw [radialToLp_norm_sq lower positive.le bounded.le,
    intervalIntegral.integral_of_le bounded.le, intervalIntegral.integral_of_le bounded.le,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
  rw [actualRadialSecond_eq_deriv lower positive bounded mode parameter source high core same radius inside]

theorem actualSecondRadialEnergy_bound (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core) (mode : ℤ) :
    actualSecondRadialEnergy lower positive bounded parameter source core mode ≤
      4 * ((lower⁻¹) ^ 2 * ‖weightedRadialCoordinate 1 lower 1
        (diskRadial lower positive bounded.le mode (highRobinWeakInverse parameter source).val)‖ ^ 2 +
        ((mode : ℝ) ^ 4 * (lower⁻¹) ^ 4 + parameter ^ 4) *
          ‖diskL2Radial lower positive bounded.le mode (highDiskBulk (highRobinWeakInverse parameter source))‖ ^ 2 +
        ‖diskL2Radial lower positive bounded.le mode source.val‖ ^ 2) := by
  have forcing : radialToLp lower (diskCoreRadialCurve mode core) (diskCoreRadialCurve mode core).continuous =
      diskL2Radial lower positive bounded.le mode source.val := by
    rw [same, diskL2Radial_core]
    rfl
  have bound : actualSecondRadialEnergy lower positive bounded parameter source core mode ≤
      4 * ((lower⁻¹) ^ 2 * ‖radialToLp lower (actualRadialSlope lower positive bounded mode parameter source)
          (actualRadialSlope lower positive bounded mode parameter source).continuous‖ ^ 2 +
        ((mode : ℝ) ^ 4 * (lower⁻¹) ^ 4 + parameter ^ 4) *
          ‖radialToLp lower (actualRadialValue lower positive bounded mode parameter source)
            (actualRadialValue lower positive bounded mode parameter source).continuous‖ ^ 2 +
        ‖radialToLp lower (diskCoreRadialCurve mode core) (diskCoreRadialCurve mode core).continuous‖ ^ 2) :=
    secondRadialCurve_energy lower positive bounded.le mode parameter
      (actualRadialValue lower positive bounded mode parameter source)
      (actualRadialSlope lower positive bounded mode parameter source) (diskCoreRadialCurve mode core)
  have slopeNorm := congrArg (fun field : RadialL2 1 lower => ‖field‖ ^ 2)
    (actualRadialSlope_stored lower positive bounded mode parameter source)
  have valueNorm := congrArg (fun field : RadialL2 1 lower => ‖field‖ ^ 2)
    (actualRadialValue_stored lower positive bounded mode parameter source)
  have forcingNorm := congrArg (fun field : RadialL2 1 lower => ‖field‖ ^ 2) forcing
  exact bound.trans_eq (congrArg₂ (fun energy forcing : ℝ => 4 * (energy + forcing))
    (congrArg₂ (fun slope value : ℝ => (lower⁻¹) ^ 2 * slope +
      ((mode : ℝ) ^ 4 * (lower⁻¹) ^ 4 + parameter ^ 4) * value) slopeNorm valueNorm) forcingNorm)

end Grad.CircularHighRegularity
