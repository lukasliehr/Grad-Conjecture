import AKCU4ActualNativeResidualSolution

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
    (radius : ℝ) (radiusPositive : 0<radius) (radiusBounded : radius≤1)
    (source : sourceSmoothRange parameters)

local notation "currentLow" => actualJetExhaustion_cubicSmall parameters parameters.length compact reference insideR seed insideS base small
local notation "nativeState" => actualJetExhaustionState parameters parameters.length compact reference insideR seed insideS base small
  compactNonnegative alphaSmall deltaSmall parameterSmall
local notation "nativeSmall" => actualNativeState_small parameters compact reference insideR seed insideS base small
  compactNonnegative alphaSmall deltaSmall parameterSmall
local notation "flatSource" => Prod.snd ((Grad.ChartAxisProjections.realRangeCoordinates radius radiusPositive radiusBounded parameters.length lengthPositive
  reference insideR seed insideS base axis) source)
local notation "residual" => actualFiniteSourceResidual parameters parameters.length (seed 0) reference insideR seed insideS base currentLow flatSource
local notation "residualFlat" => actualFiniteSourceResidual_isFlat parameters parameters.length (seed 0) lengthPositive reference insideR seed insideS base currentLow axis flatSource


/-- The actual native finite-jet residual realizes the full original source.
The reconstructed SAME-domain state is the unique preimage; the remaining
native realization hypotheses concern only the original U/S values. -/
theorem actualNative_fullOriginalSource_twoSided
    (family : NativeCartesianFamily parameters parameters.length compact lengthPositive widthHalf widthLength nativeState nativeSmall residual residualFlat)
    (constants : ℕ→ℝ) (estimate : ∀ index grade, ‖family.graded index grade‖≤constants grade)
    (vector : ACore parameters 3)
    (sameVector : ∀ (point : ClosedDisk), 0<‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters vector).value (point,(axial : CellCircle))=
        actualCartesianVectorField parameters parameters.length compact lengthPositive widthHalf widthLength nativeState nativeSmall residual residualFlat
          family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1)
          (fun index grade => Exists.intro (family.graded index grade) (family.inserted index grade)) (point.val,axial))
    (scalar : ACore parameters 1)
    (sameScalar : ∀ (point : ClosedDisk), 0<‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters scalar).value (point,(axial : CellCircle))=
        actualNativeScalarField parameters parameters.length compact lengthPositive widthHalf widthLength nativeState nativeSmall residual residualFlat
          family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1)
          (fun index grade => Exists.intro (family.graded index grade) (family.inserted index grade)) (point.val,axial))
 :
    ∃ reconstructed : stateSmoothRange parameters reference insideR,
      literalPhysicalSmoothForward parameters parameters.length reference insideR seed insideS base axis reconstructed=source ∧
      ∀ direction : stateSmoothRange parameters reference insideR,
        literalPhysicalSmoothForward parameters parameters.length reference insideR seed insideS base axis direction=source →
          reconstructed=direction := by
  obtain ⟨correction,residualLaw⟩ := actualNativeResidual_referenceSolution parameters compact lengthPositive widthHalf widthLength
    reference insideR seed insideS base axis small compactNonnegative alphaSmall deltaSmall parameterSmall
    flatSource family constants estimate vector sameVector scalar sameScalar
  obtain ⟨flatProof,forwardLaw,unique⟩ := actualFiniteJet_fullOriginalSource_twoSided parameters compact lengthPositive widthHalf widthLength
    reference insideR seed insideS base axis small compactNonnegative alphaSmall deltaSmall parameterSmall
    radius radiusPositive radiusBounded source correction residualLaw
  exact ⟨_,forwardLaw,unique⟩

end Grad.OriginalCoreRealization
