import AJC19OriginalSharedInverseConsumer
import AJE11GenuineGraphOuterTupleMap

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
open scoped Topology ENNReal
namespace Grad.AnnularForwardTraces
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularFluxTrace Grad.AnnularOmegaGraph
open Grad.AnnularCurrentBoundary Grad.AnnularLowEnergy Grad.AnnularStrongData
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularCrossMaps
open Grad.ActualBoundaryPrimitives Grad.BoundaryKernelAction Grad.AnnularTiltedReference

section HilbertProjections
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]

def traceHilbertFirst : WithLp 2 (E × F) →L[ℂ] E :=
  (ContinuousLinearMap.fst ℂ E F).comp (WithLp.prodContinuousLinearEquiv 2 ℂ E F).toContinuousLinearMap

def traceHilbertSecond : WithLp 2 (E × F) →L[ℂ] F :=
  (ContinuousLinearMap.snd ℂ E F).comp (WithLp.prodContinuousLinearEquiv 2 ℂ E F).toContinuousLinearMap

end HilbertProjections

/-- Isometric zero extension of the actual negative-half high flux trace
into the original P_R derivative coordinates. -/
def highFluxBoundaryEmbedding (parameters : PhaseParameters) :
    AnnularBoundary →L[ℂ] HighBoundaryPrimitive parameters 0 0 :=
  (highBoundaryIntoPositive parameters 0 0).toContinuousLinearMap.codRestrict
    (highAngularSubmodule parameters 0 0 1) (by
      intro field mode low
      change _ • highBoundaryIntoPositive parameters 0 0 field mode = 0
      rw [highBoundaryIntoPositive_low parameters 0 0 field mode (by omega),smul_zero])

theorem highFluxBoundaryEmbedding_high (parameters : PhaseParameters)
    (field : AnnularBoundary) (mode : HighAnnularMode) :
    (highFluxBoundaryEmbedding parameters field).val mode.val = field mode :=
  highBoundaryIntoPositive_high parameters 0 0 field mode

theorem highFluxBoundaryEmbedding_norm (parameters : PhaseParameters) (field : AnnularBoundary) :
    ‖highFluxBoundaryEmbedding parameters field‖ = ‖field‖ :=
  (highBoundaryIntoPositive parameters 0 0).norm_map field

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)

/-- The genuine outer high X trace of an arbitrary completed retained
candidate, using its actual weak derivative graph. -/
def coupledHighFluxOuter : CoupledSpace lower length positive lengthPositive →L[ℂ]
    HighBoundaryPrimitive parameters 0 0 :=
  (highFluxBoundaryEmbedding parameters).comp
    ((annularFluxTrace lower positive (lowerHalf.trans_lt (by norm_num)) 1).comp
      ((annularOmegaIntoNu lower length positive lengthPositive).comp
        (traceHilbertSecond.comp traceHilbertFirst)))

theorem coupledHighFluxOuter_coefficient
    (candidate : CoupledSpace lower length positive lengthPositive) (mode : HighAnnularMode) :
    (coupledHighFluxOuter parameters lower length positive lowerHalf lengthPositive candidate).val mode.val =
      annularFluxTrace lower positive (lowerHalf.trans_lt (by norm_num)) 1
        (annularOmegaIntoNu lower length positive lengthPositive candidate.ofLp.1.ofLp.2) mode :=
  highFluxBoundaryEmbedding_high parameters _ mode

/-- The actual positive-half Xi outer trace of the same retained candidate. -/
def coupledHighXiOuter : CoupledSpace lower length positive lengthPositive →L[ℂ]
    PositiveTrace parameters 0 0 1 :=
  (actualCurrentHighOuterTrace parameters lower length positive lowerHalf lengthPositive 0 0).comp
    (traceHilbertFirst.comp traceHilbertFirst)

/-- Original high incoming datum, with its exact inverse tilt. -/
def originalHighIncomingTrace : OriginalCoupledSpace lower length positive →L[ℂ] AnnularBoundary :=
  (lower ^ (9 / 4 : ℝ)) •
    ((annularEnergyTrace lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0).comp
      ((bEnergyDecode lower length positive).comp
        ((traceHilbertFirst.comp traceHilbertFirst).comp
          (originalCoupledEquivalence parameters lower length positive
            (lowerHalf.trans (by norm_num)) lengthPositive).toContinuousLinearMap)))

/-- Original low incoming d/Rk coordinates, using the proved BF5
normalization inverse and the genuine bounded weak-graph trace. -/
def originalLowIncomingTrace : OriginalCoupledSpace lower length positive →L[ℂ] LowEnergyBoundary :=
  (originalLowIncomingUnweightMap parameters lower length positive
    (lowerHalf.trans (by norm_num)) lengthPositive).comp
      ((lowIncomingTrace lower length positive (lowerHalf.trans_lt (by norm_num))).comp
        (traceHilbertSecond.comp
          (originalCoupledEquivalence parameters lower length positive
            (lowerHalf.trans (by norm_num)) lengthPositive).toContinuousLinearMap))

end Grad.AnnularForwardTraces
