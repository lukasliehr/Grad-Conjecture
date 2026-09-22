import AKCH9NativePolarDivergenceTransport
import AKBE10ActualObservedCartesianDeterminant

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

variable (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      originalExhaustionPrimitiveRadius parameters length compact)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (fields : ∀ index, OriginalFiveBlockAmbient parameters (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index))


variable
    (member : ∀ index, fields index ∈ OriginalObservedEquationGraph parameters length compact
      (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index)
      (originalExhaustionRadius_half length lengthPositive index) lengthPositive widthHalf widthLength state)
    (sameSources : ∀ index, (fields index).ofLp.2 =
      (cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0).val.ofLp.1)
    (allGrades : ∀ index grade : ℕ, ∃ weighted : CoupledSpace (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index) lengthPositive,
      CoupledInsertedGrade (originalExhaustionRadius length index) length
        (originalExhaustionRadius_positive length lengthPositive index) lengthPositive grade
        (originalWeightedRetainedObservation parameters (originalExhaustionRadius length index) length
          (originalExhaustionRadius_positive length lengthPositive index)
          ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index)) weighted)


open Grad.ActualCartesianDescent Grad.ClosedJets Grad.DiskExtension.Operator Grad.BoundaryTrace Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.PuncturedRetainedEnergy
variable (compatible : ∀ first second (included : originalExhaustionRadius length first ≤ originalExhaustionRadius length second),
      originalFiveBlockRestriction parameters (originalExhaustionRadius length first) (originalExhaustionRadius length second) length
        (originalExhaustionRadius_positive length lengthPositive first) (originalExhaustionRadius_positive length lengthPositive second)
        ((originalExhaustionRadius_half length lengthPositive second).trans_lt (by norm_num)) lengthPositive included (fields first) = fields second)

include compatible
open Grad.ActualCartesianFlux Grad.NonlinearRange

variable (core : ACore parameters 3)
    (same : ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters core).value (point,(axial : CellCircle)) =
        actualCartesianVectorField parameters length compact lengthPositive widthHalf widthLength state small
          source flat fields member sameSources allGrades (point.val,axial))

open Grad.OriginalKernelHomogeneousGraph Grad.ActualDeterminantEquations Grad.ActualCartesianWeakEquations
open Grad.Constraints Grad.NonlinearQuotientBounds Grad.FinitePhysicalJetLift Grad.AxisSplit

variable (physicalState : QuotientState parameters)
    (sameBase : physicalState.2.1=planarReferenceCore parameters+state.val.val.field)
    (sameEpsilon : physicalState.1=(state.val.val.epsilon : ℂ)) (scalar : ACore parameters 1)

include same sameBase sameEpsilon in
/-- The actual original solved source, evaluated by the literal original
smooth-core determinant derivative. No determinant PDE premise is added. -/
theorem actualRecoveredVector_determinant_polar (index : ℕ) (radius : ℝ)
    (inside : radius∈Ioo (originalExhaustionRadius length index) 1) (angles : ℝ×ℝ) :
    coreValue (quotientRowsDerivative parameters length 1 physicalState ![(0,core,scalar)] 2)
      (Grad.SourceCollarDivision.polarClosedPoint radius angles.1
        ((originalExhaustionRadius_positive length lengthPositive index).le.trans inside.1.le) inside.2.le) angles.2 0=
      corePolarValue parameters (source 2) radius
        ((originalExhaustionRadius_positive length lengthPositive index).le.trans inside.1.le) inside.2.le angles 0 := by
  let lower := originalExhaustionRadius length index
  let positive := originalExhaustionRadius_positive length lengthPositive index
  let bounded := (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num : (1:ℝ)/2<1)
  let coefficientSmall := originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small
  let inverseSmall := originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small
  let seven := actualCartesianSevenCurves parameters length compact lower positive
    (originalExhaustionRadius_half length lengthPositive index) lengthPositive widthHalf widthLength state inverseSmall
    coefficientSmall source flat (fields index) (member index) (sameSources index) (allGrades index)
  let flux := (samePolarCofactorVector parameters length compact lower positive bounded state seven).cartesianCovariant
  let fluxCore := originalCartesianCofactorFluxCore length physicalState core
  have sameFlux : ∀ (radius : ℝ) (included : radius∈Icc lower 1) (angles : ℝ×ℝ),
      coreValue fluxCore (Grad.SourceCollarDivision.polarClosedPoint radius angles.1 (positive.le.trans included.1) included.2) angles.2=
        flux.fullField bounded (radius,angles) := by
    intro radius included angles
    apply nativeCofactor_sameOriginalCore parameters length compact lengthPositive.ne' state coefficientSmall lower positive bounded seven
      physicalState sameBase sameEpsilon core radius included angles
    exact (actualRecoveredVector_polar parameters length compact lengthPositive widthHalf widthLength state small source flat
      fields member sameSources allGrades compatible core same index radius included angles.1 angles.2).symm
  have divergence := originalNative_divergence_polar parameters length lower positive bounded flux fluxCore sameFlux radius inside
  rw [originalQuotientDeterminant_cofactorDivergence parameters length lengthPositive.ne',
    originalCore_removeAngular_polar parameters lower positive bounded _ radius ⟨inside.1.le,inside.2.le⟩ angles]
  change removePolarMean (fun query => coreValue (originalCartesianDivergenceCore length fluxCore)
      (Grad.SourceCollarDivision.polarClosedPoint radius query.1 (positive.le.trans inside.1.le) inside.2.le) query.2 0) angles=_
  simp_rw [divergence]
  exact actualObserved_originalDeterminant parameters length compact lower positive
    (originalExhaustionRadius_half length lengthPositive index) lengthPositive widthHalf widthLength state inverseSmall coefficientSmall
    source flat (fields index) (member index) (sameSources index) (allGrades index) seven radius inside angles

end Grad.OriginalCoreRealization
