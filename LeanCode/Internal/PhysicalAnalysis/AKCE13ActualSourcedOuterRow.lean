import AKCE12NativeOuterOriginalRowConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set
open scoped ContDiff
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives
open Grad.AnnularForwardTraces Grad.AnnularPhysicalSolution Grad.AnnularStrongData Grad.AnnularSourceGraph
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularCrossMaps Grad.AnnularCurrentBoundary
open Grad.AnnularCurrentSource Grad.AnnularStrongOrbit Grad.OriginalKernelOuterUniqueness Grad.AnnularSmoothCore
open Grad.ActualSmoothPhysicalField Grad.OriginalKernelCovariantRecovery Grad.Constraints Grad.Cor18 Grad.PhysicalCoordinates
open Grad.AnnularHighGenerators
open Grad.AnnularWeightedSmoothCore Grad.OriginalKernelRetainedDecay
open Grad.AnnularGeneralSourceRegularity Grad.AnnularPhysicalFourier Grad.SourceCollarFullSource

open Grad.AnnularRestriction Grad.AnnularOriginalHigh Grad.AnnularFullGraph Grad.AnnularWeakExhaustion
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation

/-- The independently stored original source graphs are unchanged by the proved
original-to-strong isomorphism. -/
theorem strongKnownGraphPair_original (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0<lower) (bounded : lower<1) (lengthPositive : 0<length)
    (data : OriginalStrongCarrier parameters lower 0 0) :
    WithLp.toLp 2 (strongKnownGraphPair parameters lower positive bounded
      (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 data))=
      data.val.ofLp.1.ofLp.1 := by
  rw [originalStrongWeightEquivalence_eq_reconstruction]
  rfl

variable (parameters : PhaseParameters) (compact lower : ℝ)
    (positive : 0<lower) (lowerHalf : lower≤1/2) (lengthPositive : 0<parameters.length)
    (widthHalf : parameters.gamma≤1/2) (widthLength : parameters.gamma≤Real.sqrt 5/(6*parameters.length))
    (state : RetainedInverseState parameters parameters.length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8≤
      coupledPrimitiveRadius parameters parameters.length compact)
    (coefficientSmall : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 6≤
      originalCoefficientLowRadius parameters parameters.length)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (point : OriginalFiveBlockAmbient parameters lower parameters.length positive)
    (member : point∈OriginalObservedEquationGraph parameters parameters.length compact lower positive lowerHalf lengthPositive widthHalf widthLength state)
    (sameSources : point.ofLp.2=(actualOriginalSourceDatum parameters parameters.length state.val.val.rho state.val.val.epsilon
      state.val.val.field coefficientSmall lower positive (lowerHalf.trans_lt (by norm_num)) 0 source flat).val.ofLp.1)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower parameters.length positive lengthPositive,
      CoupledInsertedGrade lower parameters.length positive lengthPositive grade
        (originalWeightedRetainedObservation parameters lower parameters.length positive (lowerHalf.trans (by norm_num)) lengthPositive point) weighted)
    (vector : ACore parameters 3)
    (insideSeed : originalCoefficientSeed parameters compact state.val.val∈Seed.parameterDomain)
    (same : ∀ angles : ℝ×ℝ,
      (((actualCartesianSevenCurves parameters parameters.length compact lower positive lowerHalf lengthPositive widthHalf widthLength state
        small coefficientSmall source flat point member sameSources allGrades).covariant parameters parameters.length compact lower positive
        (lowerHalf.trans_lt (by norm_num)) state.val).physicalUFromPolar parameters parameters.length state.val.val.rho state.val.val.epsilon
        state.val.val.field state.val.val.low lower positive (lowerHalf.trans_lt (by norm_num))).fullField
        (lowerHalf.trans_lt (by norm_num)) (1,angles)=originalCoreCircle parameters vector ⟨1,zero_le_one,le_rfl⟩ angles)
    (outer : originalOuterBoundaryTrace parameters parameters.length compact lower positive lowerHalf lengthPositive state
      (point.ofLp.1,point.ofLp.2.ofLp.1)=0)

include same outer

/-- The actual sourced observed equation and its original outer boundary enforce
precisely the physical row of the SAME recovered core. -/
theorem actualObserved_originalPhysicalRow :
    physicalRow parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed (toPhysicalCore parameters vector)=0 := by
  let bounded : lower<1 := lowerHalf.trans_lt (by norm_num)
  let datum := actualOriginalSourceDatum parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field
    coefficientSmall lower positive bounded 0 source flat
  let data := originalStrongWeightEquivalence parameters lower parameters.length positive bounded.le lengthPositive 0 0 datum
  let field := originalWeightedRetainedObservation parameters lower parameters.length positive bounded.le lengthPositive point
  let seven := actualCartesianSevenCurves parameters parameters.length compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    small coefficientSmall source flat point member sameSources allGrades
  have smooth := actualCartesianObserved_phaseWeighted_radial parameters parameters.length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small coefficientSmall source flat point member sameSources allGrades
  have graphs : WithLp.toLp 2 (strongKnownGraphPair parameters lower positive bounded data)=point.ofLp.2.ofLp.1 :=
    (strongKnownGraphPair_original parameters lower parameters.length positive bounded lengthPositive datum).trans
      (congrArg (fun value => value.ofLp.1) sameSources).symm
  have boundary : coupledFullOuterBoundary parameters parameters.length compact lower positive lowerHalf lengthPositive state field
      (WithLp.toLp 2 (strongKnownGraphPair parameters lower positive bounded data))=0 := by
    rw [graphs]
    exact (originalOuterBoundaryTrace_to_coupled parameters parameters.length compact lower positive lowerHalf lengthPositive state
      point.ofLp.1 point.ofLp.2.ofLp.1).symm.trans outer
  exact nativeOuter_originalPhysicalRow parameters compact lower positive lowerHalf lengthPositive state data field
    allGrades smooth seven vector insideSeed same boundary

end Grad.OriginalCoreRealization
