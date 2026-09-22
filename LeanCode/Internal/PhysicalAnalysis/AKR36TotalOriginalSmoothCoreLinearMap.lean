import AKR35ExactTupleObservationRealLinearity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 400000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularOriginalSmoothCore Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.PhaseAlgebra
open Grad.AnnularOriginalHigh Grad.AnnularOriginalLow Grad.AnnularLowEnergy Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.WeightedTrace

open Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger

open Grad.AnnularCurrentLow Grad.AnnularCurrentSource Grad.AnnularHighTilt

open Grad.AnnularFullGraph

open Grad.AnnularHighRadial Grad.AnnularTiltedReference Grad.AnnularOmegaGraph Grad.CircularHighRegularity

open Grad.AnnularCurrentLow
open Grad.AnnularCurrentSource
open Grad.AnnularStrongData
open Grad.AnnularForwardDatum Grad.AnnularForwardTraces Grad.AnnularStrongOrbit
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (lengthPositive : 0 < length) (state : RetainedInverseState parameters length compact)

/-- The total real linear original graph map on the literal four-field
smooth core, carrying computed AH24 residuals in exactly the five norms. -/
def originalTupleGraphLinear : OriginalSmoothTuple parameters lower →ₗ[ℝ]
    OriginalFiveBlockAmbient parameters lower length positive where
  toFun tuple := originalTupleGraphImage parameters length compact lower positive bounded state tuple
  map_add' first second := originalTupleObservation_unique
    (originalTupleGraphImage_represents parameters length compact lower positive bounded state (first+second) lengthPositive)
    (originalTupleObservation_add
      (originalTupleGraphImage_represents parameters length compact lower positive bounded state first lengthPositive)
      (originalTupleGraphImage_represents parameters length compact lower positive bounded state second lengthPositive))
  map_smul' scalar tuple := originalTupleObservation_unique
    (originalTupleGraphImage_represents parameters length compact lower positive bounded state (scalar • tuple) lengthPositive)
    (originalTupleObservation_real_smul scalar
      (originalTupleGraphImage_represents parameters length compact lower positive bounded state tuple lengthPositive))

theorem originalTupleGraphLinear_represents (tuple : OriginalSmoothTuple parameters lower) :
    OriginalTupleObservation parameters length compact lower positive bounded lengthPositive state tuple
      (originalTupleGraphLinear parameters length compact lower positive bounded lengthPositive state tuple) :=
  originalTupleGraphImage_represents parameters length compact lower positive bounded state tuple lengthPositive

/-- The actual graph norm has precisely retained X, source F0 H1;1, source
F2 H1;0, full F1 L0, and strengthened full G3 L1 coordinates. -/
theorem originalTupleGraphLinear_norm_sq (tuple : OriginalSmoothTuple parameters lower) :
    ‖originalTupleGraphLinear parameters length compact lower positive bounded lengthPositive state tuple‖^2 =
      ‖tupleOriginalRetained parameters lower length positive bounded tuple‖^2 +
      ‖tupleOriginalSourceGraph parameters lower positive bounded tuple 2 1 0‖^2 +
      ‖tupleOriginalSourceGraph parameters lower positive bounded tuple 3 0 0‖^2 +
      ‖tupleOriginalF1 parameters length compact lower positive bounded state tuple‖^2 +
      ‖tupleOriginalG3 parameters length compact lower positive bounded state tuple‖^2 :=
  originalFiveBlock_norm_sq parameters lower length positive
    (originalTupleGraphLinear parameters length compact lower positive bounded lengthPositive state tuple)

end Grad.AnnularOriginalCoreRealization
