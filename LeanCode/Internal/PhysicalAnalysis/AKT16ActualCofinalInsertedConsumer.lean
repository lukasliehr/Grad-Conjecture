import AKT12ActualCartesianAllGradeAnnularWitnesses

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.ActualPuncturedFamily
open Grad.CartesianState Grad.AnnularFullGraph Grad.AnnularForwardDatum Grad.AnnularStrongOrbit
open Grad.AnnularForwardTraces Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularRestriction
open Grad.AnnularExhaustionEstimate Grad.AnnularWeakExhaustion Grad.AnnularFullSource
open Grad.AnnularHighGenerators Grad.AnnularCrossOrbit Grad.ActualAnnularExhaustion
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.SourceCollarFullSource Grad.ExhaustionSourceAllocation
open Grad.GaugeCoefficients.Physical.Allocation
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  traceCoupledRealNormed traceCoupledRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule
  sourceRadialRealInner sourceGraphRealInner sourceKnownGraphRealInner
  weakRetainedRealInner weakSourcesRealInner weakFiveRealInner

attribute [local instance] weakWeightedRetainedRealInner
attribute [local instance] Grad.AnnularStrongOrbit.knownAmbientNormed Grad.AnnularStrongOrbit.knownAmbientSeminormed Grad.AnnularStrongOrbit.knownAmbientRealNormed Grad.AnnularStrongOrbit.knownAmbientRealModule
  Grad.AnnularStrongOrbit.strongCarrierNormed Grad.AnnularStrongOrbit.strongCarrierSeminormed Grad.AnnularStrongOrbit.strongCarrierRealNormed Grad.AnnularStrongOrbit.strongCarrierRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace
  Grad.AnnularCrossOrbit.coupledNormed Grad.AnnularCrossOrbit.coupledSeminormed
  Grad.AnnularCrossOrbit.coupledComplexNormed Grad.AnnularCrossOrbit.coupledComplexModule
  Grad.AnnularCrossOrbit.coupledRealNormed Grad.AnnularCrossOrbit.coupledRealModule
  Grad.AnnularCrossOrbit.coupledOperatorRealNormed Grad.AnnularCrossOrbit.coupledOperatorRealModule





/-- Direct bridge between the existing original annular solve insertion
and its actual full-five-block retained observation. -/
theorem originalExhaustionInserted_observation
    (parameters : PhaseParameters) (length compact : ℝ)
    (context : CoupledCoordinateContext parameters length compact) (grade : ℕ)
    (data : OriginalStrongCarrier parameters context.lower 0 0)
    (weighted : CoupledSpace context.lower length context.positive context.lengthPositive)
    (actual : ExhaustionRetainedInserted parameters length compact context grade data weighted) :
    CoupledInsertedGrade context.lower length context.positive context.lengthPositive grade
      (originalWeightedRetainedObservation parameters context.lower length context.positive
        (context.lowerHalf.trans (by norm_num)) context.lengthPositive
        (originalExhaustionSolve parameters length compact context data)) weighted := actual

/-- The actual Cartesian-cofinal insertion is exactly the insertion of
AKP's fixed-state full solution, with the same datum and all copied sources. -/
theorem cartesianExhaustionInserted_observation
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      originalExhaustionPrimitiveRadius parameters length compact)
    (source : SmoothQuotient parameters) (flat : IsFlat source) (grade index : ℕ)
    (weighted : CoupledSpace (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index) lengthPositive)
    (actual : ExhaustionRetainedInserted parameters length compact
      (cartesianExhaustionContext parameters length compact lengthPositive widthHalf widthLength state small index) grade
      (cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0) weighted) :
    CoupledInsertedGrade (originalExhaustionRadius length index) length (originalExhaustionRadius_positive length lengthPositive index) lengthPositive grade
      (originalWeightedRetainedObservation parameters (originalExhaustionRadius length index) length
        (originalExhaustionRadius_positive length lengthPositive index)
        ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive
        (fixedExhaustionSolve parameters length compact lengthPositive widthHalf widthLength state
          (originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
          (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index)
          (originalExhaustionRadius_half length lengthPositive index)
          (cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0))) weighted :=
  originalExhaustionInserted_observation parameters length compact
    (cartesianExhaustionContext parameters length compact lengthPositive widthHalf widthLength state small index) grade
    (cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0) weighted actual

end Grad.ActualPuncturedFamily
