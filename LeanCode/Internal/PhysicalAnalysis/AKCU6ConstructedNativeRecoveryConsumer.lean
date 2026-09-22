import AKCU5ActualOriginalTwoSidedSource

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace Grad.OriginalCoreRealization
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





open Grad.AnnularKernelContinuity
open Grad.AnnularPhysicalReconstruction Grad.AnnularKernelL2 Grad.SourceCollarDivision


open Grad.ActualPuncturedReconstruction Grad.AnnularCurrentEnergy

open Grad.ActualPuncturedFamily Grad.ActualPhysicalField


open Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.ActualCartesianDescent Grad.BoundaryTrace Grad.SourceBoundaryTrace
open Grad.FinitePhysicalJetLift Grad.OriginalKernelRetainedDecay Grad.OriginalKernelCovariantRecovery
open Grad.PhysicalCoordinates Grad.SourceCollar Grad.Constraints Grad.Cor18 Grad.NonlinearRange
open Grad.ActualCartesianFlux

open Grad.NonlinearQuotientBounds Grad.RealFixedRanges Grad.Q24Realization Grad.OriginalCurrentInverseUniqueness

variable (parameters : PhaseParameters) (compact : ℝ)
    (lengthPositive : 0<parameters.length) (widthHalf : parameters.gamma≤1/2)
    (widthLength : parameters.gamma≤Real.sqrt 5/(6*parameters.length))
    (reference : Seed.Parameters) (insideR : reference∈Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed∈Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (small : physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
      (seed 0) base.1 8≤actualJetExhaustionRadius parameters parameters.length compact)
    (compactNonnegative : 0≤compact) (alphaSmall : |seed 1|≤compact)
    (deltaSmall : |seed 2|≤compact) (parameterSmall : |seed 3|≤compact)
    (source : OriginalFlatSource parameters parameters.length)
    (bounded : physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
      (seed 0) base.1 20≤1)
local notation "currentLow" => actualJetExhaustion_cubicSmall parameters parameters.length compact reference insideR seed insideS base small
local notation "nativeState" => actualJetExhaustionState parameters parameters.length compact reference insideR seed insideS base small
  compactNonnegative alphaSmall deltaSmall parameterSmall
local notation "nativeSmall" => actualNativeState_small parameters compact reference insideR seed insideS base small
  compactNonnegative alphaSmall deltaSmall parameterSmall
local notation "residual" => actualFiniteSourceResidual parameters parameters.length (seed 0) reference insideR seed insideS base currentLow source
local notation "residualFlat" => actualFiniteSourceResidual_isFlat parameters parameters.length (seed 0) lengthPositive reference insideR seed insideS base currentLow axis source

include bounded axis lengthPositive widthHalf widthLength small compactNonnegative alphaSmall deltaSmall parameterSmall

/-- The existing AN3 family has uniformly bounded actual inserted grades. -/
theorem actualNativeFamily_bounded :
    ∃ (family : NativeCartesianFamily parameters parameters.length compact lengthPositive widthHalf widthLength nativeState nativeSmall residual residualFlat)
      (constants : ℕ→ℝ),
      ∀ index grade, ‖family.graded index grade‖≤constants grade := by
  obtain ⟨constant,nonnegative,baseConstant,baseNonnegative,solve⟩ :=
    actualFiniteJet_exhaustion_twenty parameters parameters.length compact lengthPositive
  obtain ⟨family,high,baseBound⟩ := solve widthHalf widthLength reference insideR seed insideS base axis
    compactNonnegative alphaSmall deltaSmall parameterSmall small bounded source
  let constants : ℕ→ℝ := fun grade => constant grade *
    (‖quotientEta parameters (grade+20) (source).val.val‖ +
      physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
        (seed 0) base.1 (grade+20)*‖quotientEta parameters 20 (source).val.val‖)
  have estimate : ∀ index grade, ‖family.graded index grade‖≤constants grade := by
    intro index grade
    refine (show ‖family.graded index grade‖≤family.nativeNorm index grade from ?_).trans (high index grade)
    unfold NativeCartesianFamily.nativeNorm exhaustionDatumNorm originalWeightedDatumNorm
    exact le_add_of_nonneg_left (norm_nonneg _)
  exact ⟨family,constants,estimate⟩

end Grad.OriginalCoreRealization
