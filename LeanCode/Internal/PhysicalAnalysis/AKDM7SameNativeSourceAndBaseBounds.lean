import AKDM6RecoveredCovariantPureCellEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.FinitePhysicalJetLift
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




/-- One SAME solve carries all native estimates and its exact independent
retained bound, so original-core recovery can reuse it without a new choice. -/
theorem actualCartesianSource_nativeFamily_withBase
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length) :
    ∃ constant : ℕ → ℝ, (∀ t, 0 ≤ constant t) ∧
      ∀ (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
        (state : RetainedInverseState parameters length compact)
        (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
          originalExhaustionPrimitiveRadius parameters length compact)
        (_stateBound : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 14 ≤ 1)
        (source : SmoothQuotient parameters) (flat : IsFlat source) (_vanishing : SourceHigherVanishing source),
        ∃ family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat,
          (∀ k t, family.nativeNorm k t ≤ constant t * (‖quotientEta parameters (t + 8) source‖ +
            physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (t + 14) *
              ‖quotientEta parameters 8 source‖)) ∧
          (∀ k, family.nativeNorm k 0 ≤ (2*constant 0)*‖quotientEta parameters 8 source‖) ∧
          (∀ k, originalWeightedRetainedNorm parameters (originalExhaustionRadius length k) length
            (originalExhaustionRadius_positive length lengthPositive k)
            ((originalExhaustionRadius_half length lengthPositive k).trans (by norm_num)) lengthPositive (family.limit k).ofLp.1 ≤
              2*independentCoupledDataConstant parameters length compact *
                (originalSourceAllocationConstant parameters length 0*(1+1)*‖quotientEta parameters 8 source‖)) := by
  obtain ⟨constant,nonnegative,solve⟩ := actualCartesianSource_compatibleSolution parameters length compact lengthPositive 1 (by norm_num)
  refine ⟨fun t => originalSourceAllocationConstant parameters length t + constant t,
    fun t => add_nonneg (originalSourceAllocationConstant_positive parameters length t).le (nonnegative t), ?_⟩
  intro widthHalf widthLength state small stateBound source flat vanishing
  obtain ⟨limit,graded,equations,compatible,inserted⟩ := solve widthHalf widthLength state small stateBound source flat vanishing
  let family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat :=
    ⟨(limit,graded), (fun k => ⟨(equations k).1,(equations k).2.1,(equations k).2.2.1⟩),
      compatible, (fun k t => (inserted k t).1)⟩
  have high : ∀ k t, family.nativeNorm k t ≤
      (originalSourceAllocationConstant parameters length t+constant t) *
        (‖quotientEta parameters (t+8) source‖+
          physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (t+14)*
            ‖quotientEta parameters 8 source‖) := by
    intro k t
    have datum := actualOriginalSourceDatum_EX_bound parameters length state.val.val.rho state.val.val.epsilon lengthPositive
      state.val.val.field (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho
        state.val.val.epsilon state.val.val.field small) t (originalExhaustionRadius length k)
      (originalExhaustionRadius_positive length lengthPositive k)
      ((originalExhaustionRadius_half length lengthPositive k).trans_lt (by norm_num)) source flat vanishing
    have retained := (inserted k t).2
    change family.nativeNorm k t ≤ _
    unfold NativeCartesianFamily.nativeNorm
    change _ + ‖graded k t‖ ≤ _
    change exhaustionDatumNorm parameters length compact
      (cartesianExhaustionContext parameters length compact lengthPositive widthHalf widthLength state small k)
      (cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat k t) ≤ _ at datum
    nlinarith only [datum,retained]
  refine ⟨family,high,?_,fun k => (equations k).2.2.2⟩
  intro k
  have h := high k 0
  have cost0 : 0≤originalSourceAllocationConstant parameters length 0+constant 0 :=
    add_nonneg (originalSourceAllocationConstant_positive parameters length 0).le (nonnegative 0)
  have smallProduct := mul_le_mul_of_nonneg_right stateBound (norm_nonneg (quotientEta parameters 8 source))
  change family.nativeNorm k 0 ≤
    (originalSourceAllocationConstant parameters length 0+constant 0) *
      (‖quotientEta parameters 8 source‖+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 14*‖quotientEta parameters 8 source‖) at h
  nlinarith only [h,mul_le_mul_of_nonneg_left smallProduct cost0]

end Grad.FinitePhysicalJetLift
