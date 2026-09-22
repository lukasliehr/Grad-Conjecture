import AKEG6SameRetainedNativeNorm

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




variable {parameters : PhaseParameters} {length compact : ℝ} {lengthPositive : 0 < length}
    {widthHalf : parameters.gamma ≤ 1 / 2} {widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)}
    {state : RetainedInverseState parameters length compact}
    {small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      originalExhaustionPrimitiveRadius parameters length compact}
    {source : SmoothQuotient parameters} {flat : IsFlat source}


/-- The existing residual-native estimate on an arbitrary SAME family supplies
all rough-row hypotheses; the finite M is only an auxiliary PDE-construction bound. -/
theorem NativeCartesianFamily.roughRowBounds
    (family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state small source flat)
    (cost : ℕ → ℝ) (costNonnegative : ∀ grade,0 ≤ cost grade)
    (nativeBound : ∀ index grade, family.nativeNorm index grade ≤ cost grade *
      (‖quotientEta parameters (grade+8) source‖+
        physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+14)*
          ‖quotientEta parameters 8 source‖))
    (low : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 14 ≤ 1) :
    ∃ M : ℝ, 0 ≤ M ∧ physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 14 ≤ M ∧
      (∀ index, originalWeightedRetainedNorm parameters (originalExhaustionRadius length index) length
        (originalExhaustionRadius_positive length lengthPositive index)
        ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive
        (family.limit index).ofLp.1 ≤ 2*independentCoupledDataConstant parameters length compact *
          (originalSourceAllocationConstant parameters length 0*(1+M)*‖quotientEta parameters 8 source‖)) ∧
      ∃ constants : ℕ → ℝ, ∀ index grade, ‖family.graded index grade‖ ≤ constants grade := by
  let independent := independentCoupledDataConstant parameters length compact
  let allocation := originalSourceAllocationConstant parameters length 0
  let budget := physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 14
  have independentPositive : 0 < independent := nativeIndependentDataConstant_positive parameters length compact
  have allocationPositive : 0 < allocation := originalSourceAllocationConstant_positive parameters length 0
  have budgetNonnegative : 0 ≤ budget := physicalBudget_nonnegative _ _ _ _ _
  have denominatorPositive : 0 < independent*allocation := mul_pos independentPositive allocationPositive
  let M := budget+cost 0/(independent*allocation)
  have Mnonnegative : 0 ≤ M := add_nonneg budgetNonnegative (div_nonneg (costNonnegative 0) denominatorPositive.le)
  have budgetBound : budget ≤ M := le_add_of_nonneg_right (div_nonneg (costNonnegative 0) denominatorPositive.le)
  have ratioBound : cost 0/(independent*allocation) ≤ 1+M := by
    dsimp [M]
    linarith only [budgetNonnegative]
  have costBound : cost 0 ≤ independent*allocation*(1+M) := by
    have paid := (div_le_iff₀ denominatorPositive).mp ratioBound
    simpa only [mul_comm] using paid
  refine ⟨M,Mnonnegative,budgetBound,?_,?_,?_⟩
  · intro index
    have original := (family.retainedNorm_le_nativeNorm index).trans (nativeBound index 0)
    have smallProduct := mul_le_mul_of_nonneg_right low (norm_nonneg (quotientEta parameters 8 source))
    have baseBound : family.nativeNorm index 0 ≤ (2*cost 0)*‖quotientEta parameters 8 source‖ := by
      have estimate := nativeBound index 0
      change family.nativeNorm index 0 ≤ cost 0*(‖quotientEta parameters 8 source‖+budget*‖quotientEta parameters 8 source‖) at estimate
      have product := mul_le_mul_of_nonneg_left smallProduct (costNonnegative 0)
      nlinarith only [estimate,product]
    apply ((family.retainedNorm_le_nativeNorm index).trans baseBound).trans
    have paid := mul_le_mul_of_nonneg_right costBound (norm_nonneg (quotientEta parameters 8 source))
    change (2*cost 0)*‖quotientEta parameters 8 source‖ ≤ 2*independent*(allocation*(1+M)*‖quotientEta parameters 8 source‖)
    nlinarith only [paid]
  · exact fun grade => cost grade*(‖quotientEta parameters (grade+8) source‖+
      physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+14)*‖quotientEta parameters 8 source‖)
  · intro index grade
    apply le_trans _ (nativeBound index grade)
    unfold NativeCartesianFamily.nativeNorm exhaustionDatumNorm originalWeightedDatumNorm
    exact le_add_of_nonneg_left (norm_nonneg _)

end Grad.FinitePhysicalJetLift
