import AJC16SharedPhysicalWeakGraph
import AED3ExactPhaseDerivativeTransport
import AAW1WeakEndpointDifferentiation
import AJI5ActualFluxContinuousBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology
namespace Grad.AnnularHighRadial
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularReconstruction Grad.AnnularHighTilt Grad.AnnularTiltedReference
open Grad.AnnularRegularity Grad.CircularHighRegularity Grad.AnnularFluxTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The exact original r^(9/4) exp(-Phi) storage removal. -/
def rawHighPhase (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (cell : ℤ) : C(ℝ, ℝ) :=
  highPowerCurve lower highTiltExponent positive * annularInversePhase parameters cell

def rawHighPhaseSlope (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (cell : ℤ) : C(ℝ, ℝ) :=
  highPowerSlopeCurve lower highTiltExponent positive * annularInversePhase parameters cell +
    highPowerCurve lower highTiltExponent positive * annularInversePhaseSlope parameters cell

theorem rawHighPhase_hasDerivAt (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (cell : ℤ) (radius : ℝ) : HasDerivAt (rawHighPhase parameters lower positive cell)
      (rawHighPhaseSlope parameters lower positive cell radius) radius :=
  (highPowerCurve_hasDerivAt lower highTiltExponent positive radius).mul
    (annularInversePhase_hasDerivAt parameters cell radius)

theorem rawHighPhaseSlope_cancel (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (cell : ℤ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    rawHighPhaseSlope parameters lower positive cell radius =
      -(rawHighPhase parameters lower positive cell radius * annularTiltCurve parameters lower positive cell radius) := by
  change highPowerSlopeCurve lower highTiltExponent positive radius * annularInversePhase parameters cell radius +
    highPowerCurve lower highTiltExponent positive radius *
      (-annularPhaseSlope parameters cell radius * annularInversePhase parameters cell radius) = _
  rw [highPowerSlope_logarithmic lower highTiltExponent positive radius inside]
  change _ = -((highPowerCurve lower highTiltExponent positive radius * annularInversePhase parameters cell radius) *
    (annularPhaseSlope parameters cell radius - highTiltExponent / max lower radius))
  ring

theorem rawHighPhase_compensated (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (cell : ℤ) (value : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower (rawHighPhaseSlope parameters lower positive cell) value =
      -(collarScalar 1 lower (rawHighPhase parameters lower positive cell)
        (collarScalar 1 lower (annularTiltCurve parameters lower positive cell) value)) := by
  apply Lp.ext
  filter_upwards [collarScalar_ae 1 lower (rawHighPhaseSlope parameters lower positive cell) value,
    collarScalar_ae 1 lower (rawHighPhase parameters lower positive cell)
      (collarScalar 1 lower (annularTiltCurve parameters lower positive cell) value),
    collarScalar_ae 1 lower (annularTiltCurve parameters lower positive cell) value,
    Lp.coeFn_neg (collarScalar 1 lower (rawHighPhase parameters lower positive cell)
      (collarScalar 1 lower (annularTiltCurve parameters lower positive cell) value)),
    ae_restrict_mem measurableSet_Icc] with radius slope phase tilt negative inside
  rw [slope, negative, Pi.neg_apply, phase, tilt, rawHighPhaseSlope_cancel parameters lower positive cell radius inside,
    neg_smul, mul_smul]

/-- Actual storage removal cancels exactly the tilted zeroth-order term. -/
theorem rawHighPhase_weak (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (cell : ℤ) (value forcing : CollarL2 (ComplexEuclidean 1) lower)
    (weak : CollarWeakDerivative lower value
      (collarScalar 1 lower (annularTiltCurve parameters lower positive cell) value + forcing)) :
    CollarWeakDerivative lower (collarScalar 1 lower (rawHighPhase parameters lower positive cell) value)
      (collarScalar 1 lower (rawHighPhase parameters lower positive cell) forcing) := by
  have transformed := collarWeakDerivative_scalar lower (rawHighPhase parameters lower positive cell)
    (rawHighPhaseSlope parameters lower positive cell) (rawHighPhase_hasDerivAt parameters lower positive cell)
    value _ weak
  rw [map_add, rawHighPhase_compensated, neg_add_cancel_left] at transformed
  exact transformed

end Grad.AnnularHighRadial
