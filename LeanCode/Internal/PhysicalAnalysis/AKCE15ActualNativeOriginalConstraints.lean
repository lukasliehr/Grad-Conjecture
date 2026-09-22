import AKCE14SameRecoveredOriginalOuterRow
import AKAN2NativeCompatibleJetFamily
import AKCA16ActualRecoveredVectorGauges
import AKCA18ActualOriginalScalarMean
import AKCA11ActualRecoveredVectorFirstJets

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
open Grad.ActualCartesianFlux

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

include sameVector

/-- The actual compatible solved family has the original physical outer row;
no boundary premise is added to its stored equations. -/
theorem nativeFamily_recoveredOuter :
    physicalRow parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed (toPhysicalCore parameters vector)=0 :=
  actualRecoveredVector_physicalRow parameters parameters.length compact lengthPositive widthHalf widthLength state small source flat
    family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1) (fun index grade => Exists.intro (family.graded index grade) (family.inserted index grade)) family.compatible vector sameVector rfl insideSeed (family.equations 0).2.2

/-- Every original complex vector constraint follows for this SAME recovered
native vector, using its proved critical energy and actual outer equation. -/
theorem nativeFamily_recoveredVectorConstraints (vanishing : SourceHigherVanishing source)
    (constants : ℕ→ℝ) (estimate : ∀ index grade, ‖family.graded index grade‖≤constants grade) :
    VectorConstraints parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed (toPhysicalCore parameters vector) := by
  have gauges := actualRecoveredVector_gauges parameters parameters.length compact lengthPositive widthHalf widthLength state small source flat
    family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1) (fun index grade => Exists.intro (family.graded index grade) (family.inserted index grade)) family.compatible vector sameVector rfl insideSeed
  refine ⟨?_,gauges.1,gauges.2,nativeFamily_recoveredOuter parameters compact lengthPositive widthHalf widthLength state small source flat
    family vector sameVector insideSeed⟩
  exact toPhysicalCore_zeroJets parameters vector
    (actualRecoveredVector_zeroFirstJets parameters parameters.length compact lengthPositive widthHalf widthLength state small source flat
      family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1) (fun index grade => Exists.intro (family.graded index grade) (family.inserted index grade)) family.compatible vanishing family.graded family.inserted constants estimate vector sameVector)

/-- SAME recovered physical U and corrected S satisfy the complete original
complex constraints. Reality remains a separate original-domain obligation. -/
theorem nativeFamily_recoveredFullConstraints (vanishing : SourceHigherVanishing source)
    (constants : ℕ→ℝ) (estimate : ∀ index grade, ‖family.graded index grade‖≤constants grade)
    (scalar : ACore parameters 1)
    (sameScalar : ∀ (point : ClosedDisk), 0<‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters scalar).value (point,(axial : CellCircle))=
        actualNativeScalarField parameters parameters.length compact lengthPositive widthHalf widthLength state small source flat
          family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1) (fun index grade => Exists.intro (family.graded index grade) (family.inserted index grade)) (point.val,axial)) :
    FullConstraints parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed
      (0,toPhysicalCore parameters vector,scalar) := by
  exact ⟨nativeFamily_recoveredVectorConstraints parameters compact lengthPositive widthHalf widthLength state small source flat family
    vector sameVector insideSeed vanishing constants estimate,
    actualRecoveredScalar_mean parameters parameters.length compact lengthPositive widthHalf widthLength state small source flat family.limit
      (fun index => (family.equations index).1) (fun index => (family.equations index).2.1) (fun index grade => Exists.intro (family.graded index grade) (family.inserted index grade)) family.compatible scalar sameScalar⟩

end Grad.OriginalCoreRealization
