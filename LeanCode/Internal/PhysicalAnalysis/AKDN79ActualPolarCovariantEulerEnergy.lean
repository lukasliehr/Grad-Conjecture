import AKDN78UniformActualSevenEnergy
import AKDN70ActualCovariantJointEnergy
import AKCD6SameNativeCovariantGlobalEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.OriginalCartesianTameEstimate
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

/-- Literal normalized covariant reconstruction applied to the SAME actual input. -/
theorem nativePolarCovariant_jointSourceEnergy
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
    (∫⁻ radius in Icc (originalExhaustionRadius length index) 1, ENNReal.ofReal
      (‖(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+extra)) •
        vectorEulerWithinIteratedDerivative (Icc (originalExhaustionRadius length index) 1) rank
          (((nativeSevenCurves family index).covariant parameters length compact (originalExhaustionRadius length index)
            (originalExhaustionRadius_positive length lengthPositive index)
            ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) state.val).curve power) radius‖^2)) ≤
      ENNReal.ofReal ((constant*(‖quotientEta parameters (total+10) source‖+
        (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (total+16))*‖quotientEta parameters 9 source‖))^2) := by
  let lower := originalExhaustionRadius length index
  let positive := originalExhaustionRadius_positive length lengthPositive index
  let bounded : lower<1 := (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)
  let inputs := nativeSevenCurves_uniformJointEnergy parameters length compact lengthPositive widthHalf widthLength index total cost cost0
  let inputConstant := inputs.choose
  have input0 : 0 ≤ inputConstant := inputs.choose_spec.1
  have inputBound := inputs.choose_spec.2
  let kernel := fun (state : AnnularReconstructionState parameters length compact) radius =>
    radialNormalizedCovariantKernel parameters length compact state.val radius state.property
  let reconstruction := originalNormalizedCovariantEulerFamily parameters length compact
  have smooth : ∀ state, SmoothConjugatedFamily parameters lower positive bounded.le (kernel state) :=
    fun state => radialNormalizedCovariantKernel_conjugated_smooth parameters length compact state lower positive bounded
  obtain ⟨actionConstant,action0,actionBound⟩ := actualEulerFamily_jointEnergy parameters length compact lower positive bounded
    kernel reconstruction smooth total extra power rank paid
  refine ⟨actionConstant*inputConstant,mul_nonneg action0 input0,?_⟩
  intro state low small source flat family native
  let payment := ‖quotientEta parameters (total+10) source‖+
    (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (total+16))*‖quotientEta parameters 9 source‖
  have payment0 : 0≤payment := add_nonneg (norm_nonneg _) (mul_nonneg
    (add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)) (norm_nonneg _))
  have unit := (physicalBudget_monotone parameters state.val.val.field state.val.val.rho state.val.val.epsilon (by norm_num : 10≤15)).trans low
  have actual := actionBound state unit (nativeSevenCurves family index).curve
    (nativeSevenCurves family index).smooth
    (fun grade reserve radius inside mode => (nativeSevenCurves family index).shift bounded grade reserve radius inside mode)
    (inputConstant*payment) (mul_nonneg input0 payment0)
    (fun j p r allocated => inputBound state low small source flat family native j p r allocated)
  exact actual.trans_eq (by congr 1; ring)

end Grad.OriginalCartesianTameEstimate
