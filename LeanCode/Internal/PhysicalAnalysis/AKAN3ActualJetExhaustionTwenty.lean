import AKAN2NativeCompatibleJetFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.FinitePhysicalJetLift
open Grad.ActualPuncturedFamily Grad.Constraints Grad.Q24Realization Grad.AxisSplit Grad.ChartAxisLift Grad.ConstrainedTransfer Grad.NonlinearQuotientBounds
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




/-- Native twenty-loss EX after the exact original finite jet correction.
One actual current and one constructed compatible family serve every collar
and every grade. The separate base bound contains only the fixed F20 norm. -/
theorem actualFiniteJet_exhaustion_twenty
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length) :
    ∃ constant : ℕ → ℝ, (∀ t, 0 ≤ constant t) ∧
      ∃ baseConstant : ℝ, 0 ≤ baseConstant ∧
      ∀ (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
        (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
        (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
        (base : RealJointCore parameters reference insideR)
        (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
        (compactNonnegative : 0 ≤ compact) (alphaSmall : |seed 1| ≤ compact)
        (deltaSmall : |seed 2| ≤ compact) (parameterSmall : |seed 3| ≤ compact)
        (small : physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
          (seed 0) base.1 8 ≤ actualJetExhaustionRadius parameters length compact)
        (_bounded : physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
          (seed 0) base.1 20 ≤ 1)
        (source : OriginalFlatSource parameters length),
        let low := actualJetExhaustion_cubicSmall parameters length compact reference insideR seed insideS base small
        let state := actualJetExhaustionState parameters length compact reference insideR seed insideS base small
          compactNonnegative alphaSmall deltaSmall parameterSmall
        let exSmall := actualJetExhaustion_exSmall parameters length compact reference insideR seed insideS base small
        let residual := actualFiniteSourceResidual parameters length (seed 0) reference insideR seed insideS base low source
        let flat := actualFiniteSourceResidual_isFlat parameters length (seed 0) lengthPositive reference insideR seed insideS base low axis source
        ∃ family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state exSmall residual flat,
          (∀ k t, family.nativeNorm k t ≤ constant t *
            (‖quotientEta parameters (t + 20) source.val.val‖ +
              physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
                (seed 0) base.1 (t + 20) * ‖quotientEta parameters 20 source.val.val‖)) ∧
          (∀ k, family.nativeNorm k 0 ≤ baseConstant * ‖quotientEta parameters 20 source.val.val‖) := by
  obtain ⟨nativeConstant,nativeNonnegative,nativeSolve⟩ := actualCartesianSource_nativeFamily parameters length compact lengthPositive
  choose paymentConstant paymentNonnegative paymentBound using actualFiniteSourceResidual_exhaustion_payment parameters length
  obtain ⟨lowConstant,lowNonnegative,lowBound⟩ := originalRealFiniteLiftResidual_low_payment parameters length
  refine ⟨fun t => nativeConstant t * paymentConstant t,
    fun t => mul_nonneg (nativeNonnegative t) (paymentNonnegative t),
    2 * nativeConstant 0 * lowConstant, mul_nonneg (mul_nonneg (by norm_num) (nativeNonnegative 0)) lowNonnegative, ?_⟩
  intro widthHalf widthLength reference insideR seed insideS base axis compactNonnegative alphaSmall deltaSmall parameterSmall small bounded source
  dsimp only
  let field := actualFiniteCurrentField parameters reference insideR seed insideS base
  let low := actualJetExhaustion_cubicSmall parameters length compact reference insideR seed insideS base small
  let state := actualJetExhaustionState parameters length compact reference insideR seed insideS base small
    compactNonnegative alphaSmall deltaSmall parameterSmall
  let exSmall := actualJetExhaustion_exSmall parameters length compact reference insideR seed insideS base small
  let residual := actualFiniteSourceResidual parameters length (seed 0) reference insideR seed insideS base low source
  let flat := actualFiniteSourceResidual_isFlat parameters length (seed 0) lengthPositive reference insideR seed insideS base low axis source
  have vanishing := actualFiniteSourceResidual_higherVanishing parameters length (seed 0) lengthPositive reference insideR seed insideS base low axis source
  have stateBound : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 14 ≤ 1 :=
    (physicalBudget_monotone parameters field (seed 0) base.1 (by norm_num : 14 ≤ 20)).trans bounded
  obtain ⟨family,native⟩ := nativeSolve widthHalf widthLength state exSmall stateBound residual flat vanishing
  refine ⟨family, ?_, ?_⟩
  · intro k t
    have increase := mul_le_mul_of_nonneg_right
      (physicalBudget_monotone parameters field (seed 0) base.1 (by omega : t + 14 ≤ t + 20))
      (norm_nonneg (quotientEta parameters 8 residual))
    have payment := paymentBound t (seed 0) base.1 field low bounded
      (actualFiniteCurrentScalar parameters reference insideR seed insideS base) source.val.val
    change ‖quotientEta parameters (t + 8) residual‖ +
      physicalBudget parameters field (seed 0) base.1 (t + 20) * ‖quotientEta parameters 8 residual‖ ≤ _ at payment
    have inputBound := (add_le_add (le_refl (‖quotientEta parameters (t + 8) residual‖)) increase).trans payment
    have estimate := (native k t).trans (mul_le_mul_of_nonneg_left inputBound (nativeNonnegative t))
    exact estimate.trans_eq (by ring)
  · intro k
    have smallResidual := lowBound (seed 0) base.1 field low bounded
      (actualFiniteCurrentScalar parameters reference insideR seed insideS base) source.val.val
    change ‖quotientEta parameters 8 residual‖ ≤ lowConstant * ‖quotientEta parameters 20 source.val.val‖ at smallResidual
    have lowProduct := mul_le_mul_of_nonneg_right stateBound (norm_nonneg (quotientEta parameters 8 residual))
    have inputBound : ‖quotientEta parameters (0 + 8) residual‖ +
        physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (0 + 14) *
          ‖quotientEta parameters 8 residual‖ ≤ 2 * (lowConstant * ‖quotientEta parameters 20 source.val.val‖) := by
      change ‖quotientEta parameters 8 residual‖ +
        physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 14 *
          ‖quotientEta parameters 8 residual‖ ≤ 2 * (lowConstant * ‖quotientEta parameters 20 source.val.val‖)
      nlinarith only [smallResidual,lowProduct]
    have estimate := (native k 0).trans (mul_le_mul_of_nonneg_left inputBound (nativeNonnegative 0))
    exact estimate.trans_eq (by ring)

end Grad.FinitePhysicalJetLift
