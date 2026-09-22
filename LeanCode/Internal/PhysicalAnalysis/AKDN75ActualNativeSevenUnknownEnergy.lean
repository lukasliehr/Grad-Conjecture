import AKDN73ActualStoredSevenFidelity
import AKDN72BalancedSevenAssemblyEnergy
import AKDN66ActualNativeBalancedSourceEnergy

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
open scoped ENNReal BigOperators
attribute [local irreducible] originalWeightedDatum

open Grad.AnnularSmoothCore

/-- The actual homogeneous part of the seven packet inherits the SAME
balanced native estimate, using just one fixed extra frequency grade. -/
theorem nativeBalancedInput_originalSourceEnergy
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
          (fun point => balancedSevenInput parameters point (nativeBalancedCurve family index (power+1) point)) radius‖^2)) ≤
      ENNReal.ofReal ((constant*(‖quotientEta parameters (total+10) source‖+
        (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (total+16))*‖quotientEta parameters 9 source‖))^2) := by
  let lower := originalExhaustionRadius length index
  let positive := originalExhaustionRadius_positive length lengthPositive index
  let bounded : lower<1 := (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)
  let nativeResult := nativeBalancedCurve_originalSourceEnergy parameters length compact lengthPositive widthHalf widthLength
    index (total+1) (by omega) cost cost0
  let nativeConstant := nativeResult.choose
  have native0 : 0≤nativeConstant := nativeResult.choose_spec.1
  have nativeBound := nativeResult.choose_spec.2
  obtain ⟨assembly,assembly0,assemblyBound⟩ := balancedInputCurve_squareEnergy parameters lower positive bounded rank
  refine ⟨assembly*nativeConstant,mul_nonneg assembly0 native0,?_⟩
  intro state low small source flat family native
  let weight := 1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+extra)
  let payment := ‖quotientEta parameters (total+10) source‖+
    (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (total+16))*‖quotientEta parameters 9 source‖
  have weight0 : 0≤weight := add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)
  have payment0 : 0≤payment := add_nonneg (norm_nonneg _)
    (mul_nonneg (add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)) (norm_nonneg _))
  have actual := assemblyBound (nativeBalancedCurve family index (power+1)) (nativeBalancedCurve_smooth family index (power+1))
    weight (nativeConstant*payment) weight0 (mul_nonneg native0 payment0) (by
      intro order orderLe
      have actual := nativeBound state low small source flat family native extra (power+1) order (by omega)
      simpa only [show total+1+9=total+10 by omega,show total+1+15=total+16 by omega] using actual)
  exact actual.trans_eq (by congr 1; ring)

end Grad.OriginalCartesianTameEstimate
