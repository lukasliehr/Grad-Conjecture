import AKDM7SameNativeSourceAndBaseBounds
import AKDB13ActualNativeOriginalCoreAssembly
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

open Grad.OriginalCartesianTameEstimate

/-- The actual compatible source solve, its SAME original cores and its
pure-cell bound are obtained together. Constants precede the state and source. -/
theorem actualCartesianSource_covariantXiScalar_quantitative
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length) :
    ∃ nativeConstant cellConstant : ℕ → ℝ,
    (∀ grade, 0≤nativeConstant grade) ∧ (∀ grade, 0≤cellConstant grade) ∧
    ∀ (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
      (state : RetainedInverseState parameters length compact)
      (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
        originalExhaustionPrimitiveRadius parameters length compact)
      (_stateBound : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 14 ≤ 1)
      (source : SmoothQuotient parameters) (flat : IsFlat source) (_vanishing : SourceHigherVanishing source)
      (_low : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 <
        actualNativeAllOrderRadius parameters length compact lengthPositive state.val.val.compactNonnegative),
    ∃ family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat,
      (∀ index grade, family.nativeNorm index grade ≤ nativeConstant grade *
        (‖quotientEta parameters (grade+8) source‖+
          physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+14)*‖quotientEta parameters 8 source‖)) ∧
      (∀ index, family.nativeNorm index 0 ≤ (2*nativeConstant 0)*‖quotientEta parameters 8 source‖) ∧
    ∃ covariant : ACore parameters 3, ∃ xi scalar : ACore parameters 1,
      (∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ cell : ℤ,
        (covariant.val cell).value point=actualCartesianCovariantCell parameters length compact lengthPositive widthHalf widthLength state small
          source flat family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1)
          (fun index grade => ⟨family.graded index grade,family.inserted index grade⟩) cell point.val) ∧
      (∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
        (originalPhysicalClosedJet parameters covariant).value (point,(axial : CellCircle))=
          actualCartesianCovariantFamilyField parameters length compact lengthPositive widthHalf widthLength state small
            source flat family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1)
            (fun index grade => ⟨family.graded index grade,family.inserted index grade⟩) (point.val,axial)) ∧
      (∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
        (originalPhysicalClosedJet parameters xi).value (point,(axial : CellCircle))=
          actualCartesianXiFamilyField parameters length compact lengthPositive widthHalf widthLength state small
            source flat family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1)
            (fun index grade => ⟨family.graded index grade,family.inserted index grade⟩) (point.val,axial)) ∧
      (∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
        (originalPhysicalClosedJet parameters scalar).value (point,(axial : CellCircle))=
          actualNativeScalarField parameters length compact lengthPositive widthHalf widthLength state small
            source flat family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1)
            (fun index grade => ⟨family.graded index grade,family.inserted index grade⟩) (point.val,axial)) ∧
      ∀ grade, originalCellNorm parameters grade covariant ≤ cellConstant grade *
        (‖quotientEta parameters (grade+8) source‖+
          physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+14)*‖quotientEta parameters 8 source‖) := by
  let certificate := actualCartesianSource_nativeFamily_withBase parameters length compact lengthPositive
  let nativeConstant := certificate.choose
  have nativeNonnegative := certificate.choose_spec.1
  have solve := certificate.choose_spec.2
  let endpoint (grade : ℕ) := Real.sqrt (2*Real.pi)*nativeCovariantEndpointConstant parameters length compact grade
  have endpointNonnegative (grade : ℕ) : 0≤endpoint grade :=
    mul_nonneg (Real.sqrt_nonneg _) (nativeCovariantEndpointConstant_nonnegative parameters length compact lengthPositive grade)
  let cellConstant := fun grade => endpoint grade*(nativeConstant grade+2*nativeConstant 0)
  refine ⟨nativeConstant,cellConstant,nativeNonnegative,
    (fun grade => mul_nonneg (endpointNonnegative grade)
      (add_nonneg (nativeNonnegative grade) (mul_nonneg (by norm_num) (nativeNonnegative 0)))),?_⟩
  intro widthHalf widthLength state small stateBound source flat vanishing low
  let solved := solve widthHalf widthLength state small stateBound source flat vanishing
  let family := solved.choose
  have nativeBound := solved.choose_spec.1
  have baseBound := solved.choose_spec.2.1
  have retainedBound := solved.choose_spec.2.2
  let payment := fun grade => nativeConstant grade *
    (‖quotientEta parameters (grade+8) source‖+
      physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+14)*‖quotientEta parameters 8 source‖)
  have paymentNonnegative (grade : ℕ) : 0≤payment grade := mul_nonneg (nativeNonnegative grade)
    (add_nonneg (norm_nonneg _) (mul_nonneg (physicalBudget_nonnegative _ _ _ _ _) (norm_nonneg _)))
  have gradedBound : ∀ index grade, ‖family.graded index grade‖ ≤ payment grade := by
    intro index grade
    apply le_trans _ (nativeBound index grade)
    unfold NativeCartesianFamily.nativeNorm exhaustionDatumNorm originalWeightedDatumNorm
    exact le_add_of_nonneg_left (norm_nonneg _)
  let coreResult := actualNative_covariantXiScalar_cores parameters length compact lengthPositive widthHalf widthLength state small source flat
      family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1)
      (fun index grade => ⟨family.graded index grade,family.inserted index grade⟩) family.compatible
      1 (by norm_num) stateBound vanishing retainedBound family.graded family.inserted payment gradedBound low
  let covariant := coreResult.choose
  let xi := coreResult.choose_spec.choose
  let scalar := coreResult.choose_spec.choose_spec.choose
  have identities := coreResult.choose_spec.choose_spec.choose_spec
  have covariantCells := identities.1
  have covariantSame := identities.2.1
  have xiSame := identities.2.2.1
  have scalarSame := identities.2.2.2
  refine ⟨family,nativeBound,baseBound,covariant,xi,scalar,covariantCells,covariantSame,xiSame,scalarSame,?_⟩
  have small12 := (physicalBudget_monotone parameters state.val.val.field state.val.val.rho state.val.val.epsilon
    (by norm_num : 12≤14)).trans stateBound
  have estimate := recoveredCovariant_originalCellEndpoint family small12 covariant covariantCells payment paymentNonnegative
    nativeBound ((2*nativeConstant 0)*‖quotientEta parameters 8 source‖)
    (mul_nonneg (mul_nonneg (by norm_num) (nativeNonnegative 0)) (norm_nonneg _)) baseBound
  intro grade
  have coefficientBound := mul_le_mul_of_nonneg_right
    (physicalBudget_monotone parameters state.val.val.field state.val.val.rho state.val.val.epsilon
      (by omega : grade+12≤grade+14))
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) (nativeNonnegative 0)) (norm_nonneg (quotientEta parameters 8 source)))
  have extraNonnegative := mul_nonneg
    (mul_nonneg (by norm_num : (0:ℝ)≤2) (nativeNonnegative 0)) (norm_nonneg (quotientEta parameters (grade+8) source))
  have inside : payment grade+
      physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+12)*
        ((2*nativeConstant 0)*‖quotientEta parameters 8 source‖) ≤
      (nativeConstant grade+2*nativeConstant 0)*
        (‖quotientEta parameters (grade+8) source‖+
          physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+14)*‖quotientEta parameters 8 source‖) := by
    dsimp only [payment]
    nlinarith only [coefficientBound,extraNonnegative]
  exact (estimate grade).trans ((mul_le_mul_of_nonneg_left inside (endpointNonnegative grade)).trans_eq
    (by dsimp only [cellConstant,endpoint]; ring))

end Grad.ActualScaledNativeCoefficients
