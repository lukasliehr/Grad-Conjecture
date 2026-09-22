import AKDN64SameNativeJointEulerEnergy
import AKDN65OriginalNativeEnergyPayment

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

/-- Actual integrated native balanced Euler bound, paid by the original
source with fixed loss nine and an independent F9 base. -/
theorem nativeBalancedCurve_originalSourceEnergy
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (index total : ℕ) (totalPositive : 0 < total)
    (cost : ℕ → ℝ) (cost0 : ∀ rank,0≤cost rank) :
    ∃ constant : ℝ, 0≤constant ∧
    ∀ state : RetainedInverseState parameters length compact,
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 15 ≤ 1 →
    ∀ (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
        originalExhaustionPrimitiveRadius parameters length compact)
      (source : SmoothQuotient parameters) (flat : IsFlat source)
      (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat),
    (∀ rank, family.nativeNorm index rank ≤ cost rank*(‖quotientEta parameters (rank+8) source‖+
      physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (rank+14)*‖quotientEta parameters 8 source‖)) →
    ∀ extra grade order : ℕ, extra+grade+order ≤ total →
    (∫⁻ radius in Icc (originalExhaustionRadius length index) 1, ENNReal.ofReal
      (‖(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+extra)) •
        vectorEulerWithinIteratedDerivative (Icc (originalExhaustionRadius length index) 1) order
          (nativeBalancedCurve family index grade) radius‖^2)) ≤
      ENNReal.ofReal ((constant*(‖quotientEta parameters (total+9) source‖+
        (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (total+15))*‖quotientEta parameters 9 source‖))^2) := by
  let result := nativeBalancedCurve_jointEulerEnergy parameters length compact lengthPositive widthHalf widthLength index total totalPositive
  let constant := result.choose
  have constant0 : 0≤constant := result.choose_spec.1
  have bound := result.choose_spec.2
  let multiplier := cost (total+1)+2*cost 1+1
  have multiplier0 : 0≤multiplier := add_nonneg (add_nonneg (cost0 _) (mul_nonneg (by norm_num) (cost0 _))) zero_le_one
  refine ⟨constant*multiplier,mul_nonneg constant0 multiplier0,?_⟩
  intro state low small source flat family nativeBound extra grade order allocated
  have unit := (physicalBudget_monotone parameters state.val.val.field state.val.val.rho state.val.val.epsilon
    (by norm_num : 10≤15)).trans low
  have energy := bound state unit small source flat family extra grade order allocated
  have payment := nativeJointPayment_bound parameters length compact state source total cost cost0
    (family.nativeNorm index) nativeBound low
  have native0 (rank : ℕ) : 0≤family.nativeNorm index rank := by
    unfold NativeCartesianFamily.nativeNorm exhaustionDatumNorm originalWeightedDatumNorm
    exact add_nonneg (norm_nonneg _) (norm_nonneg _)
  have budget0 (rank : ℕ) : 0≤1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon rank :=
    add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)
  have source0 : 0≤‖quotientEta parameters (total+9) source‖+
      (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (total+15))*‖quotientEta parameters 9 source‖ :=
    add_nonneg (norm_nonneg _) (mul_nonneg (budget0 _) (norm_nonneg _))
  apply energy.trans
  apply ENNReal.ofReal_le_ofReal
  apply (sq_le_sq₀ (mul_nonneg constant0 (add_nonneg
    (add_nonneg (native0 _) (mul_nonneg (budget0 _) (native0 _)))
    (add_nonneg (norm_nonneg _) (mul_nonneg (budget0 _) (norm_nonneg _)))))
    (mul_nonneg (mul_nonneg constant0 multiplier0) source0)).mpr
  exact (mul_le_mul_of_nonneg_left payment constant0).trans_eq (mul_assoc _ _ _).symm

end Grad.OriginalCartesianTameEstimate
