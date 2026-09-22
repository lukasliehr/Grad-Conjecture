import AKDB14ActualSourceOriginalCoreConsumer
import AKDF3ActualOriginalVectorCore
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 3000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualScaledNativeCoefficients
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

open Grad.ActualPuncturedFamily Grad.ActualPhysicalField Grad.ActualSmoothPhysicalField

open Grad.ActualCartesianDescent Grad.ClosedJets Grad.DiskExtension.Operator Grad.BoundaryTrace Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients

open Grad.CartesianStartup Grad.GaugeCoefficients.Physical.RadialLedger Grad.Constraints.Gauges
open Grad.ActualOriginalSourceMoments Grad.ActualScalarWeakEquations Grad.ActualCurrentPrimitives
open Grad.PhysicalFamily Grad.PDEBootstrap Grad.ActualForceMoments


open Grad.SpatialDilation
open Grad.AnalyticWeights.Calculus
open Grad.FinitePhysicalJetLift Grad.OriginalCoreRealization Grad.ActualCartesianWeakEquations

/-- Actual source has a SAME compatible native family and genuine original U/S cores. -/
theorem actualCartesianSource_vectorScalar_cores
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
    (M : ℝ) (Mnonnegative : 0 ≤ M)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      originalExhaustionPrimitiveRadius parameters length compact)
    (stateBound : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 14 ≤ M)
    (source : SmoothQuotient parameters) (flat : IsFlat source) (vanishing : SourceHigherVanishing source)
    (low : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 <
      actualNativeAllOrderRadius parameters length compact lengthPositive state.val.val.compactNonnegative) :
    ∃ family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat,
    ∃ constants : ℕ → ℝ,
      (∀ index grade, ‖family.graded index grade‖ ≤ constants grade) ∧
    ∃ vector : ACore parameters 3, ∃ scalar : ACore parameters 1,
      (∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
        (originalPhysicalClosedJet parameters vector).value (point,(axial : CellCircle))=
          actualCartesianVectorField parameters length compact lengthPositive widthHalf widthLength state small
            source flat family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1)
            (fun index grade => ⟨family.graded index grade,family.inserted index grade⟩) (point.val,axial)) ∧
      (∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
        (originalPhysicalClosedJet parameters scalar).value (point,(axial : CellCircle))=
          actualNativeScalarField parameters length compact lengthPositive widthHalf widthLength state small
            source flat family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1)
            (fun index grade => ⟨family.graded index grade,family.inserted index grade⟩) (point.val,axial)) := by
  let result := actualCartesianSource_covariantXiScalar_cores parameters length compact lengthPositive M Mnonnegative
    widthHalf widthLength state small stateBound source flat vanishing low
  let family := result.choose
  let constants := result.choose_spec.choose
  have data := result.choose_spec.choose_spec
  let covariant := data.2.2.choose
  let scalar := data.2.2.choose_spec.choose_spec.choose
  have identities := data.2.2.choose_spec.choose_spec.choose_spec
  have vectorResult := actualNativeVector_of_covariantCore parameters length compact lengthPositive widthHalf widthLength state small source flat
    family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1)
    (fun index grade => ⟨family.graded index grade,family.inserted index grade⟩) family.compatible covariant identities.2.1
  exact ⟨family,constants,data.1,vectorResult.choose,scalar,vectorResult.choose_spec,identities.2.2.2⟩

end Grad.ActualScaledNativeCoefficients
