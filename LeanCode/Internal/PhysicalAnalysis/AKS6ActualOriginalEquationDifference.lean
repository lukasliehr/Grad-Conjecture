import AKS5ActualWeightedHomogeneousUniqueness

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

open Grad.AnnularHighGenerators

theorem coupledInserted_sub (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (grade : ℕ) (first second firstWeighted secondWeighted : CoupledSpace lower length positive lengthPositive)
    (firstSame : CoupledInsertedGrade lower length positive lengthPositive grade first firstWeighted)
    (secondSame : CoupledInsertedGrade lower length positive lengthPositive grade second secondWeighted) :
    CoupledInsertedGrade lower length positive lengthPositive grade (first - second) (firstWeighted - secondWeighted) := by
  refine ⟨?_, ?_, ?_⟩
  · intro index
    change firstWeighted.ofLp.1.ofLp.1.val index - secondWeighted.ofLp.1.ofLp.1.val index =
      _ • (first.ofLp.1.ofLp.1.val index - second.ofLp.1.ofLp.1.val index)
    rw [firstSame.1, secondSame.1, smul_sub]
  · intro coordinate index
    change firstWeighted.ofLp.1.ofLp.2.val coordinate index - secondWeighted.ofLp.1.ofLp.2.val coordinate index =
      _ • (first.ofLp.1.ofLp.2.val coordinate index - second.ofLp.1.ofLp.2.val coordinate index)
    rw [firstSame.2.1, secondSame.2.1, smul_sub]
  · intro coordinate index
    change firstWeighted.ofLp.2.val coordinate index - secondWeighted.ofLp.2.val coordinate index =
      _ • (first.ofLp.2.val coordinate index - second.ofLp.2.val coordinate index)
    rw [firstSame.2.2, secondSame.2.2, smul_sub]

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters length compact)

include small

/-- Subtraction takes place in the genuine original equation graph, using
the accepted linear projection onto that graph. -/
theorem originalObservedEquationGraph_sub
    (first second : OriginalFiveBlockAmbient parameters lower length positive)
    (firstEquation : first ∈ OriginalObservedEquationGraph parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state)
    (secondEquation : second ∈ OriginalObservedEquationGraph parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state) :
    first - second ∈ OriginalObservedEquationGraph parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state := by
  apply (originalEquationProjection_fixed_iff parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small _).mp
  rw [map_sub,
    (originalEquationProjection_fixed_iff parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small first).mpr firstEquation,
    (originalEquationProjection_fixed_iff parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small second).mpr secondEquation]

omit widthHalf widthLength small in
theorem originalFullOuter_sub
    (first second : OriginalFiveBlockAmbient parameters lower length positive) :
    originalOuterBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state
      ((first - second).ofLp.1,(first - second).ofLp.2.ofLp.1) =
    originalOuterBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state (first.ofLp.1,first.ofLp.2.ofLp.1) -
      originalOuterBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state (second.ofLp.1,second.ofLp.2.ofLp.1) :=
  (((originalOuterBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state).comp
    (forwardTraceInput parameters length lower positive)).map_sub first second)

end Grad.AnnularWeightedUniqueness
