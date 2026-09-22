import AKCA15SameRecoveredVectorPolar

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

open Grad.OriginalKernelCovariantRecovery Grad.SourceCollar Grad.GaugeCoefficients.Physical.Frame Grad.AnnularOriginalSmoothCore Grad.Constraints.Gauges Grad.PhysicalCoordinates
open Grad.GaugeCoefficients.Physical.Ledger Grad.ActualGaugeSigmaPrimitives Grad.ActualScaledNativeCoefficients

include same in
 theorem actualRecoveredVector_covectorMeans (radius : ℝ) (radiusPositive : 0 < radius)
    (radiusBounded : |radius|≤1) (axial : ℝ) (kind : Fin 2) :
    sourceAngularAverage (fun polar => ∑ coordinate : Fin 3,
      physicalGaugeCovector (physicalSeedMatrix state.val.val.rho state.val.val.alpha state.val.val.delta state.val.val.parameter axial)
        ((length : ℂ)⁻¹ • operatorMatrix (deriv (harmonicSeedOperator state.val.val.rho state.val.val.alpha
          state.val.val.delta state.val.val.parameter) axial))
        polar (Grad.Constraints.polarClosedPoint radius radiusBounded polar) kind coordinate *
        coreValue core (Grad.Constraints.polarClosedPoint radius radiusBounded polar) axial coordinate)=0 := by
  let index := selectedInnerCollar (originalExhaustionRadius length) (originalExhaustionRadius_tendsto length) radius radiusPositive
  have inside : radius ∈ Icc (originalExhaustionRadius length index) 1 :=
    ⟨(selectedInnerCollar_lt (originalExhaustionRadius length) (originalExhaustionRadius_tendsto length) radius radiusPositive).le,
      (le_abs_self radius).trans radiusBounded⟩
  let curves := cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index
  let collarBound := (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num : (1:ℝ)/2<1)
  let r : RadialPoint := tupleRadius (originalExhaustionRadius length index)
    (originalExhaustionRadius_positive length lengthPositive index) ⟨radius,inside⟩
  let product := originalTotalGaugeProduct parameters length compact state.val.val r kind
    (fun angles => curves.fullField collarBound (radius,angles))
  have native : sourceAngularAverage (fun polar => product (polar,axial) 0)=0 := by
    apply physicalAngularMean_zero_of_cellMeans product
      (originalTotalGaugeProduct_continuous parameters length compact state.val.val r kind _
        (curves.fullField_continuous_angles collarBound radius inside))
      (originalTotalGaugeProduct_periodic parameters length compact state.val.val r kind _
        (fun polar axial => curves.fullField_angular_shift collarBound radius polar axial))
      (originalTotalGaugeProduct_cell_periodic parameters length compact state.val.val r kind _
        (fun polar axial => curves.fullField_cell_shift collarBound radius polar axial))
    intro cell
    exact actualObservedPolarCurves_gaugeMeans parameters length compact (originalExhaustionRadius length index)
      (originalExhaustionRadius_positive length lengthPositive index) (originalExhaustionRadius_half length lengthPositive index)
      lengthPositive widthHalf widthLength state
      (originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
      (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
      source flat (fields index) (member index) (sameSources index) (allGrades index) ⟨radius,inside⟩ kind cell
  have sameProduct (polar : ℝ) : product (polar,axial) 0=
      ∑ coordinate : Fin 3,
        physicalGaugeCovector (physicalSeedMatrix state.val.val.rho state.val.val.alpha state.val.val.delta state.val.val.parameter axial)
          ((length : ℂ)⁻¹ • operatorMatrix (deriv (harmonicSeedOperator state.val.val.rho state.val.val.alpha
            state.val.val.delta state.val.val.parameter) axial))
          polar (Grad.Constraints.polarClosedPoint radius radiusBounded polar) kind coordinate *
          coreValue core (Grad.Constraints.polarClosedPoint radius radiusBounded polar) axial coordinate := by
    have nativeProduct := originalGaugeProduct_sameCorrectedU parameters length compact state.val.val
      (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index)
      collarBound curves ⟨radius,inside⟩ kind (polar,axial)
    have sameU := actualRecoveredVector_polar parameters length compact lengthPositive widthHalf widthLength state small source flat
      fields member sameSources allGrades compatible core same index radius inside polar axial
    change coreValue core (Grad.SourceCollarDivision.polarClosedPoint radius polar radiusPositive.le inside.2) axial =
      (curves.physicalUFromPolar parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
        (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index) collarBound).fullField
        collarBound (radius,polar,axial) at sameU
    rw [← sameU,divisionPolarPoint_eq_original] at nativeProduct
    exact nativeProduct
  exact (congrArg sourceAngularAverage (funext sameProduct)).symm.trans native

include same in
 theorem actualRecoveredVector_gauges (sameLength : length=parameters.length)
    (seedInside : originalCoefficientSeed parameters compact (sameLength ▸ state.val.val) ∈ Grad.Constraints.Seed.parameterDomain) :
    poloidalCorrection parameters (originalCoefficientSeed parameters compact (sameLength ▸ state.val.val)) seedInside
      (toPhysicalCore parameters core)=0 ∧
    toroidalCorrection parameters (originalCoefficientSeed parameters compact (sameLength ▸ state.val.val)) seedInside
      (toPhysicalCore parameters core)=0 := by
  subst length
  apply originalGauges_zero_of_covectorMeans parameters _ seedInside core
  intro radius positive bounded axial kind
  exact actualRecoveredVector_covectorMeans parameters parameters.length compact lengthPositive widthHalf widthLength state small source flat
    fields member sameSources allGrades compatible core same radius positive bounded axial kind

end Grad.OriginalCoreRealization
