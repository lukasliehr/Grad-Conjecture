import AKS3ActualHomogeneousGraphBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology
namespace Grad.AnnularWeightedUniqueness
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularReconstruction
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularForwardDatum Grad.AnnularForwardTraces Grad.AnnularStrongOrbit
open Grad.AnnularCoupledInverse Grad.AnnularRestriction Grad.AnnularExhaustionEstimate
open Grad.AnnularIncomingIntegrability Grad.SourceCollarDivision Grad.AnnularSourceGraph
open Grad.AnnularCurrentSource Grad.AnnularVariational Grad.AnnularLowEnergy Grad.AnnularTiltedReference
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule
  traceCoupledRealNormed traceCoupledRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule
  Grad.AnnularStrongOrbit.knownAmbientNormed Grad.AnnularStrongOrbit.knownAmbientSeminormed
  Grad.AnnularStrongOrbit.knownAmbientRealNormed Grad.AnnularStrongOrbit.knownAmbientRealModule
  Grad.AnnularStrongOrbit.strongCarrierNormed Grad.AnnularStrongOrbit.strongCarrierSeminormed
  Grad.AnnularStrongOrbit.strongCarrierRealNormed Grad.AnnularStrongOrbit.strongCarrierRealModule

open Grad.AnnularFullGraph Grad.AnnularWeakExhaustion

open Grad.ActualAnnularExhaustion

/-- Genuine homogeneous graph locality, with the full physical outer row.
The intermediate incoming datum is reconstructed by accepted AKG locality. -/
theorem originalHomogeneousGraph_restrict
    (parameters : PhaseParameters) (length compact lower upper : ℝ)
    (positiveLower : 0 < lower) (positiveUpper : 0 < upper) (upperHalf : upper ≤ 1 / 2)
    (included : lower ≤ upper) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters length compact)
    (point : OriginalFiveBlockAmbient parameters lower length positiveLower)
    (equation : point ∈ OriginalObservedEquationGraph parameters length compact lower positiveLower
      (included.trans upperHalf) lengthPositive widthHalf widthLength state)
    (sources : point.ofLp.2 = 0)
    (outer : originalOuterBoundaryTrace parameters length compact lower positiveLower (included.trans upperHalf)
      lengthPositive state (point.ofLp.1,point.ofLp.2.ofLp.1) = 0) :
    let next := originalFiveBlockRestriction parameters lower upper length positiveLower positiveUpper
      (upperHalf.trans_lt (by norm_num)) lengthPositive included point
    next ∈ OriginalObservedEquationGraph parameters length compact upper positiveUpper upperHalf lengthPositive widthHalf widthLength state ∧
    next.ofLp.2 = 0 ∧
    originalOuterBoundaryTrace parameters length compact upper positiveUpper upperHalf lengthPositive state
      (next.ofLp.1,next.ofLp.2.ofLp.1) = 0 := by
  dsimp only
  refine ⟨restrictedOriginalEquationGraph parameters length compact lower upper positiveLower positiveUpper upperHalf
    lengthPositive included widthHalf widthLength state small point equation, ?_, ?_⟩
  · change originalFullSourceRestriction parameters lower upper included point.ofLp.2 = 0
    exact (congrArg (originalFullSourceRestriction parameters lower upper included) sources).trans
      (originalFullSourceRestriction parameters lower upper included).map_zero
  · exact (originalRetainedRestriction_fullOuter lower upper length positiveLower positiveUpper upperHalf included parameters lengthPositive compact state
      point.ofLp.1 point.ofLp.2.ofLp.1).trans outer

end Grad.AnnularWeightedUniqueness
