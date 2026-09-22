import AJO1GenuineLowWeakDerivative
import AAX15InvertibleWeakConjugation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularLowClassical
open Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularRegularity
open Grad.AnnularFluxTrace Grad.CircularHighRegularity Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.AnnularReconstruction Grad.AnnularFourSource Grad.AnnularCurrentLow

/-- Continuous realization of the original balancing multiplier. -/
def lowFactorCurve (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (index : LowAnnularIndex) : C(ℝ, ℝ) :=
  if index.1 = 0 then
    (annularForwardPhase parameters index.2.val.2) *
      (lowAmplitude length parameters.gamma index.2 • lowMuCurve lower length positive index.2.val.2)
  else annularForwardPhase parameters index.2.val.2

theorem lowFactorCurve_actual (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (index : LowAnnularIndex) (radius : ℝ) (inside : lower ≤ radius) :
    lowFactorCurve parameters lower length positive index radius =
      lowPhysicalFactor parameters length radius index := by
  unfold lowFactorCurve lowPhysicalFactor
  split_ifs
  · change Real.exp _ * (lowAmplitude length parameters.gamma index.2 * lowMu length (max lower radius) index.2.val.2) = _
    rw [max_eq_right inside]
  · change Real.exp _ = Real.exp _ * 1
    rw [mul_one]

/-- Continuous logarithmic slope, recovered algebraically from the actual
common diagonal plus the physical x/r term. -/
def lowLogSlopeCurve (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (index : LowAnnularIndex) : C(ℝ, ℝ) :=
  lowMuCurve lower length positive index.2.val.2 *
    (lowCommonDiagonalCurve parameters length lower positive index +
      if index.1 = 0 then 0 else lowRadiusMuRatio lower length positive index.2.val.2)

theorem lowLogSlopeCurve_actual (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (index : LowAnnularIndex) (radius : ℝ) (inside : lower ≤ radius) :
    lowLogSlopeCurve parameters lower length positive index radius =
      lowBalancingLogSlope parameters length radius index.2 index.1 := by
  have mu : lowMuCurve lower length positive index.2.val.2 radius = lowMu length radius index.2.val.2 := by
    change lowMu length (max lower radius) _ = _
    rw [max_eq_right inside]
  change lowMuCurve lower length positive index.2.val.2 radius *
    (lowCommonDiagonalCurve parameters length lower positive index radius + _) = _
  rw [mu, lowCommonDiagonalCurve_actual parameters length lower positive index radius inside]
  unfold lowBalancingLogSlope
  by_cases first : index.1 = 0
  · simp only [first, ↓reduceIte, ContinuousMap.zero_apply, add_zero]
    field_simp [(lowMu_pos length radius index.2.val.2 (positive.trans_le inside)).ne']
  · simp only [first, ↓reduceIte]
    rw [lowRadiusMuRatio_actual lower length positive index.2.val.2 radius inside]
    field_simp [(lowMu_pos length radius index.2.val.2 (positive.trans_le inside)).ne']
    ring

/-- A continuous candidate physical RHS determines a continuous encoded
slope of the original normalized section, without assuming any derivative. -/
def lowEncodedSlopeCurve (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (field : lowEnergyGraph lower length positive)
    (index : LowAnnularIndex) (rhs : C(ℝ, ComplexEuclidean 1)) : C(ℝ, ComplexEuclidean 1) :=
  let factor := lowFactorCurve parameters lower length positive index
  let logarithmic := lowLogSlopeCurve parameters lower length positive index
  let physical := radialSectionExtension 1 lower bounded.le (lowPhysicalSection parameters lower length positive bounded field index)
  ⟨fun radius => factor radius • rhs radius + (factor radius * logarithmic radius) • physical radius,
    (factor.continuous.smul rhs.continuous).add ((factor.continuous.mul logarithmic.continuous).smul physical.continuous)⟩

theorem lowEncodedSlopeCurve_actual (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (field : lowEnergyGraph lower length positive)
    (index : LowAnnularIndex) (rhs : C(ℝ, ComplexEuclidean 1)) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    lowEncodedSlopeCurve parameters lower length positive bounded field index rhs radius =
      lowPhysicalFactor parameters length radius index • rhs radius +
        (lowPhysicalFactor parameters length radius index * lowBalancingLogSlope parameters length radius index.2 index.1) •
          lowPhysicalSection parameters lower length positive bounded field index ⟨radius, inside⟩ := by
  change lowFactorCurve parameters lower length positive index radius • rhs radius +
    (lowFactorCurve parameters lower length positive index radius * lowLogSlopeCurve parameters lower length positive index radius) • _ = _
  rw [lowFactorCurve_actual parameters lower length positive index radius inside.1,
    lowLogSlopeCurve_actual parameters lower length positive index radius inside.1,
    lowSectionExtension_eval lower bounded.le _ radius inside]

end Grad.AnnularLowClassical
