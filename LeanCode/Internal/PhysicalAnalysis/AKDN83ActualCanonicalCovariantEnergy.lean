import AKDN82SameNativeCanonicalCovariant

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.OriginalCartesianTameEstimate
open Grad.ActualCartesianWeakEquations
open Grad.ActualPuncturedFamily
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




open Grad.FinitePhysicalJetLift Grad.ActualSmoothPhysicalField Grad.ActualNativeCellMoments
open Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.ClosedJets Grad.SourceBoundaryTrace
open MeasureTheory
open scoped ENNReal BigOperators ContDiff
attribute [local irreducible] originalWeightedDatum

open Grad.AnnularSmoothCore Grad.AnnularGeneralSourceRegularity

open Grad.AnnularWeightedSmoothness Grad.BoundaryKernelAction Grad.AnnularKernelL2

open Grad.NonlinearRange Grad.ActualCartesianFlux Grad.ActualPuncturedReconstruction

/-- Actual core Euler energy with SAME native family, source and original phase. -/
theorem nativeCanonicalCovariant_jointSourceEnergy
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0<length)
    (widthHalf : parameters.gamma≤1/2) (widthLength : parameters.gamma≤Real.sqrt 5/(6*length))
    (index total extra power rank : ℕ) (paid : extra+power+rank≤total)
    (cost : ℕ → ℝ) (cost0 : ∀ order,0≤cost order) :
    ∃ constant : ℝ, 0≤constant ∧
    ∀ state : RetainedInverseState parameters length compact,
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 15≤1 →
    ∀ (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8≤
        originalExhaustionPrimitiveRadius parameters length compact)
      (source : SmoothQuotient parameters) (flat : IsFlat source)
      (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat),
    (∀ order, family.nativeNorm index order≤cost order*(‖quotientEta parameters (order+8) source‖+
      physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (order+14)*‖quotientEta parameters 8 source‖)) →
    ∀ core : ACore parameters 3,
    (∀ (point : ClosedDisk), 0<‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters core).value (point,(axial : CellCircle))=
        actualCartesianCovariantFamilyField parameters length compact lengthPositive widthHalf widthLength state small source flat
          family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1)
          (fun index grade => ⟨family.graded index grade,family.inserted index grade⟩) (point.val,axial)) →
    (∫⁻ radius in Icc (originalExhaustionRadius length index) 1, ENNReal.ofReal
      (‖(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+extra)) •
        vectorEulerWithinIteratedDerivative (Icc (originalExhaustionRadius length index) 1) rank
          (cartesianWeightedRadialCurve parameters (originalExhaustionRadius length index)
            (originalExhaustionRadius_positive length lengthPositive index)
            ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) core power 0) radius‖^2)) ≤
      ENNReal.ofReal ((constant*(‖quotientEta parameters (total+10) source‖+
        (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (total+16))*‖quotientEta parameters 9 source‖))^2) := by
  let result := nativeCovariant_jointSourceEnergy parameters length compact lengthPositive widthHalf widthLength index total extra power rank paid cost cost0
  let constant := result.choose
  have constant0 : 0≤constant := result.choose_spec.1
  have bound := result.choose_spec.2
  refine ⟨constant,constant0,?_⟩
  intro state low small source flat family native core sameCore
  have energy := bound state low small source flat family native
  have same := eulerCurve_squareEnergy_congr (originalExhaustionRadius length index)
    (cartesianWeightedRadialCurve parameters (originalExhaustionRadius length index)
      (originalExhaustionRadius_positive length lengthPositive index)
      ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) core power 0)
    ((nativeCovariantCurves family index).curve power)
    (fun radius inside => nativeCovariant_canonicalCurve family core sameCore index power radius inside) rank
    (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+extra))
  exact same.le.trans energy

end Grad.OriginalCartesianTameEstimate
