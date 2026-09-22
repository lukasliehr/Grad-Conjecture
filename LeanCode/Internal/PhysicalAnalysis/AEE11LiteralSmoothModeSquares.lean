import AEE10SmoothActualReferenceEquations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators ENNReal
namespace Grad.AnnularLowCompletion
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowVolterra
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

def lowCoreGraphDensity (length : ℝ) (core : LowAnnularIndex →₀ SmoothRadialCore 1)
    (index : LowAnnularIndex) (radius : ℝ) : ℝ :=
  radius ^ (-(7 / 2 : ℝ)) * (‖(core index).val.val.1 radius‖ ^ 2 +
    ‖(lowMu length radius index.2.val.2)⁻¹ • (core index).val.val.2 radius‖ ^ 2)

def lowCoreForceDensity (parameters : PhaseParameters) (length lower : ℝ) (positive : 0 < lower)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) (index : LowAnnularIndex) (radius : ℝ) : ℝ :=
  radius ^ (-(7 / 2 : ℝ)) * ‖lowCoreResidualCurve parameters length lower positive core index radius‖ ^ 2

def lowCoreGraphSquare (length lower : ℝ) (core : LowAnnularIndex →₀ SmoothRadialCore 1)
    (index : LowAnnularIndex) : ℝ := ∫ radius in lower..1, lowCoreGraphDensity length core index radius

def lowCoreIncomingSquare (length lower : ℝ) (core : LowAnnularIndex →₀ SmoothRadialCore 1)
    (index : LowAnnularIndex) : ℝ :=
  lowEnergyDensity length lower index.2.val.2 * ‖(core index).val.val.1 lower‖ ^ 2

def lowCoreDataSquare (parameters : PhaseParameters) (length lower : ℝ) (positive : 0 < lower)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) (index : LowAnnularIndex) : ℝ :=
  lowCoreIncomingSquare length lower core index +
    ∫ radius in lower..1, lowCoreForceDensity parameters length lower positive core index radius

theorem lowCoreGraphDensity_integrable (length lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) (index : LowAnnularIndex) :
    IntervalIntegrable (lowCoreGraphDensity length core index) volume lower 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le bounded]
  intro radius member
  have radiusPositive := positive.trans_le member.1
  have normalized := (lowMuInverse_hasDerivAt length radius index.2.val.2 radiusPositive).continuousAt.smul
    (core index).val.val.2.continuous.continuousAt
  exact ((Real.hasDerivAt_rpow_const (x := radius) (p := -(7 / 2 : ℝ)) (Or.inl radiusPositive.ne')).continuousAt.mul
    (((core index).val.val.1.continuous.continuousAt.norm.pow 2).add (normalized.norm.pow 2))).continuousWithinAt

theorem lowCoreForceDensity_integrable (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) (index : LowAnnularIndex) :
    IntervalIntegrable (lowCoreForceDensity parameters length lower positive core index) volume lower 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le bounded]
  intro radius member
  exact ((Real.hasDerivAt_rpow_const (x := radius) (p := -(7 / 2 : ℝ))
    (Or.inl (positive.trans_le member.1).ne')).continuousAt.mul
    ((lowCoreResidualCurve parameters length lower positive core index).continuous.continuousAt.norm.pow 2)).continuousWithinAt

theorem lowCoreGraphSquare_nonneg (length lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) (index : LowAnnularIndex) :
    0 ≤ lowCoreGraphSquare length lower core index :=
  intervalIntegral.integral_nonneg bounded (fun radius member =>
    mul_nonneg (Real.rpow_pos_of_pos (positive.trans_le member.1) _).le (by positivity))

theorem lowCoreDataSquare_nonneg (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) (index : LowAnnularIndex) :
    0 ≤ lowCoreDataSquare parameters length lower positive core index :=
  add_nonneg (mul_nonneg (lowEnergyDensity_pos length lower index.2.val.2 positive).le (sq_nonneg _))
    (intervalIntegral.integral_nonneg bounded (fun _radius member =>
      mul_nonneg (Real.rpow_pos_of_pos (positive.trans_le member.1) _).le (sq_nonneg _)))

end Grad.AnnularLowCompletion
