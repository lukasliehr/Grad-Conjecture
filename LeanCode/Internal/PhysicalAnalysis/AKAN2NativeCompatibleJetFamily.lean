import AKAN1SameActualJetExhaustionState

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




/-- The same actual all-grade family, with the full original observed equation,
copied four-source equality, physical outer trace, and collar compatibility. -/
def NativeCartesianFamily
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      originalExhaustionPrimitiveRadius parameters length compact)
    (source : SmoothQuotient parameters) (flat : IsFlat source) :=
  { pair :
      (∀ k, OriginalFiveBlockAmbient parameters (originalExhaustionRadius length k) length
        (originalExhaustionRadius_positive length lengthPositive k)) ×
      (∀ k (_t : ℕ), CoupledSpace (originalExhaustionRadius length k) length
        (originalExhaustionRadius_positive length lengthPositive k) lengthPositive) //
    (∀ k,
    pair.1 k ∈ OriginalObservedEquationGraph parameters length compact (originalExhaustionRadius length k)
      (originalExhaustionRadius_positive length lengthPositive k) (originalExhaustionRadius_half length lengthPositive k)
      lengthPositive widthHalf widthLength state ∧
    (pair.1 k).ofLp.2 = (cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength
      state small source flat k 0).val.ofLp.1 ∧
    originalOuterBoundaryTrace parameters length compact (originalExhaustionRadius length k)
      (originalExhaustionRadius_positive length lengthPositive k) (originalExhaustionRadius_half length lengthPositive k)
      lengthPositive state ((pair.1 k).ofLp.1,(pair.1 k).ofLp.2.ofLp.1) = 0) ∧
    (∀ k l (included : originalExhaustionRadius length k ≤ originalExhaustionRadius length l),
    originalFiveBlockRestriction parameters (originalExhaustionRadius length k) (originalExhaustionRadius length l)
      length (originalExhaustionRadius_positive length lengthPositive k) (originalExhaustionRadius_positive length lengthPositive l)
      ((originalExhaustionRadius_half length lengthPositive l).trans_lt (by norm_num)) lengthPositive included (pair.1 k) = pair.1 l) ∧
    (∀ k t, CoupledInsertedGrade (originalExhaustionRadius length k) length
    (originalExhaustionRadius_positive length lengthPositive k) lengthPositive t
    (originalWeightedRetainedObservation parameters (originalExhaustionRadius length k) length
      (originalExhaustionRadius_positive length lengthPositive k)
      ((originalExhaustionRadius_half length lengthPositive k).trans (by norm_num)) lengthPositive (pair.1 k)) (pair.2 k t)) }

variable {parameters : PhaseParameters} {length compact : ℝ} {lengthPositive : 0 < length}
    {widthHalf : parameters.gamma ≤ 1 / 2} {widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)}
    {state : RetainedInverseState parameters length compact}
    {small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      originalExhaustionPrimitiveRadius parameters length compact}
    {source : SmoothQuotient parameters} {flat : IsFlat source}

abbrev NativeCartesianFamily.limit
    (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat) := family.val.1

abbrev NativeCartesianFamily.graded
    (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat) := family.val.2

abbrev NativeCartesianFamily.equations
    (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat) := family.property.1

abbrev NativeCartesianFamily.compatible
    (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat) := family.property.2.1

abbrev NativeCartesianFamily.inserted
    (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat) := family.property.2.2

/-- Literal original independent datum norm plus the same retained inserted
solution norm, at the original analytic width. -/
def NativeCartesianFamily.nativeNorm
    (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat)
    (index grade : ℕ) : ℝ :=
  exhaustionDatumNorm parameters length compact
    (cartesianExhaustionContext parameters length compact lengthPositive widthHalf widthLength state small index)
    (cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index grade) +
      ‖family.graded index grade‖

/-- The actual compatible solve and actual copied datum share one native EX
bound. Existence, full equations, compatibility and inserted grades are proved. -/
theorem actualCartesianSource_nativeFamily
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length) :
    ∃ constant : ℕ → ℝ, (∀ t, 0 ≤ constant t) ∧
      ∀ (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
        (state : RetainedInverseState parameters length compact)
        (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
          originalExhaustionPrimitiveRadius parameters length compact)
        (_stateBound : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 14 ≤ 1)
        (source : SmoothQuotient parameters) (flat : IsFlat source) (_vanishing : SourceHigherVanishing source),
        ∃ family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat,
          ∀ k t, family.nativeNorm k t ≤ constant t * (‖quotientEta parameters (t + 8) source‖ +
            physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (t + 14) *
              ‖quotientEta parameters 8 source‖) := by
  obtain ⟨constant,nonnegative,solve⟩ := actualCartesianSource_compatibleSolution parameters length compact lengthPositive 1 (by norm_num)
  refine ⟨fun t => originalSourceAllocationConstant parameters length t + constant t,
    fun t => add_nonneg (originalSourceAllocationConstant_positive parameters length t).le (nonnegative t), ?_⟩
  intro widthHalf widthLength state small stateBound source flat vanishing
  obtain ⟨limit,graded,equations,compatible,inserted⟩ := solve widthHalf widthLength state small stateBound source flat vanishing
  let family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat :=
    ⟨(limit,graded), (fun k => ⟨(equations k).1,(equations k).2.1,(equations k).2.2.1⟩),
      compatible, (fun k t => (inserted k t).1)⟩
  refine ⟨family,fun k t => ?_⟩
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

end Grad.FinitePhysicalJetLift
