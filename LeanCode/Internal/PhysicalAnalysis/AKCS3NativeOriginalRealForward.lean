import AKCS2OriginalPhysicalReality
import AKCE15ActualNativeOriginalConstraints

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
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
open Grad.ActualCartesianFlux Grad.NonlinearQuotientBounds

variable (parameters : PhaseParameters) (compact : ℝ) (lengthPositive : 0<parameters.length)
    (widthHalf : parameters.gamma≤1/2) (widthLength : parameters.gamma≤Real.sqrt 5/(6*parameters.length))
    (state : RetainedInverseState parameters parameters.length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8≤
      originalExhaustionPrimitiveRadius parameters parameters.length compact)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (family : NativeCartesianFamily parameters parameters.length compact lengthPositive widthHalf widthLength state small source flat)


variable (vector : ACore parameters 3)
    (sameVector : ∀ (point : ClosedDisk), 0<‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters vector).value (point,(axial : CellCircle))=
        actualCartesianVectorField parameters parameters.length compact lengthPositive widthHalf widthLength state small source flat
          family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1) (fun index grade => Exists.intro (family.graded index grade) (family.inserted index grade)) (point.val,axial))
    (insideSeed : originalCoefficientSeed parameters compact state.val.val∈Seed.parameterDomain)

variable (vanishing : SourceHigherVanishing source)
    (constants : ℕ→ℝ) (estimate : ∀ index grade, ‖family.graded index grade‖≤constants grade)
    (scalar : ACore parameters 1)
    (sameScalar : ∀ (point : ClosedDisk), 0<‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters scalar).value (point,(axial : CellCircle))=
        actualNativeScalarField parameters parameters.length compact lengthPositive widthHalf widthLength state small source flat
          family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1)
          (fun index grade => Exists.intro (family.graded index grade) (family.inserted index grade)) (point.val,axial))
    (physicalState : QuotientState parameters)
    (sameBase : physicalState.2.1=planarReferenceCore parameters+state.val.val.field)
    (sameEpsilon : physicalState.1=(state.val.val.epsilon : ℂ))
    (currentReal : Grad.CartesianState.cartesianCoreConjugation parameters physicalState.2.1=physicalState.2.1)
    (sourceReal : Grad.CompletedReality.zCoreConjugation parameters source=source)

open Grad.CompletedReality Grad.RealFixedRanges
include sameVector sameScalar sameBase sameEpsilon currentReal sourceReal vanishing estimate

/-- The SAME native physical U/S lie in the original real constrained domain
and solve the complete original source. Reality is proved by uniqueness. -/
theorem nativeFamily_recoveredOriginal_realForward :
    (0,toPhysicalCore parameters vector,scalar)∈
      stateSmoothRange parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed ∧
    quotientRowsDerivative parameters parameters.length 1 physicalState ![(0,vector,scalar)]=source := by
  have constrained := nativeFamily_recoveredFullConstraints parameters compact lengthPositive widthHalf widthLength state small source flat
    family vector sameVector insideSeed vanishing constants estimate scalar sameScalar
  have forward := actualRecoveredPair_forward parameters parameters.length compact lengthPositive widthHalf widthLength state small source flat
    family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1)
    (fun index grade => Exists.intro (family.graded index grade) (family.inserted index grade)) family.compatible
    vector sameVector scalar sameScalar physicalState sameBase sameEpsilon
  have real := originalPhysicalPair_real parameters compact lengthPositive widthHalf widthLength state
    (small.trans (min_le_right _ _)) (small.trans (min_le_left _ _)) insideSeed
    physicalState sameBase sameEpsilon vector scalar constrained.1 constrained.2 source forward currentReal sourceReal
  refine ⟨?_,forward⟩
  apply (mem_stateSmoothRange parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed _).mpr
  refine ⟨fullProjection_fixes parameters _ insideSeed _ constrained,?_⟩
  apply Prod.ext
  · change smoothAxisConjugation parameters 2 0=0
    exact map_zero _
  · apply Prod.ext
    · change cartesianCoreConjugation parameters (toPhysicalCore parameters vector)=toPhysicalCore parameters vector
      rw [toPhysicalCore_conjugate,real.1]
    · exact real.2

end Grad.OriginalCoreRealization
