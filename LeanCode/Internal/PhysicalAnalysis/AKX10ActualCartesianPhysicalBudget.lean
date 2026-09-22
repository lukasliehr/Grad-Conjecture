import AKX9ActualOriginalGlobalBulk

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.ActualPuncturedReconstruction
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


open Grad.ActualPuncturedFamily

/-- A collar-independent original-width Cartesian source payment. -/
def cartesianPhysicalBulkConstant (parameters : PhaseParameters) (length compact M : ℝ) : ℝ :=
  originalReconstructionConstant parameters length compact * (1 + M) *
    ((11 + 4 * length) * (2 * independentCoupledDataConstant parameters length compact) + 3) *
    (originalSourceAllocationConstant parameters length 0 * (1 + M))

theorem cartesianPhysicalBulkConstant_nonnegative (parameters : PhaseParameters) (length compact M : ℝ)
    (lengthPositive : 0 < length) (Mnonnegative : 0 ≤ M) :
    0 ≤ cartesianPhysicalBulkConstant parameters length compact M := by
  have reconstruction := originalReconstructionConstant_nonnegative parameters length compact
  have inverse := independentCoupledDataConstant_nonnegative parameters length compact
  have allocation := (originalSourceAllocationConstant_positive parameters length 0).le
  unfold cartesianPhysicalBulkConstant
  positivity

variable (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      originalExhaustionPrimitiveRadius parameters length compact)
    (M : ℝ) (Mnonnegative : 0 ≤ M)
    (stateBound : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 14 ≤ M)
    (source : SmoothQuotient parameters) (flat : IsFlat source) (vanishing : SourceHigherVanishing source)

include Mnonnegative stateBound vanishing

/-- Every actual compatible-solution point inherits the original source
payment through the previously checked reconstruction. -/
theorem cartesianOriginalCovariants_bound (index : ℕ)
    (point : OriginalFiveBlockAmbient parameters (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index))
    (nativeBound : originalWeightedRetainedNorm parameters (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index)
      ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive point.ofLp.1 ≤
        2 * independentCoupledDataConstant parameters length compact *
          (originalSourceAllocationConstant parameters length 0 * (1 + M) * ‖quotientEta parameters 8 source‖)) :
    ‖originalGraphCovariant parameters length compact (originalExhaustionRadius length index)
      (originalExhaustionRadius_positive length lengthPositive index)
      ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive state
      (cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0) point‖ +
    ‖originalGraphRotatedCovariant parameters length compact (originalExhaustionRadius length index)
      (originalExhaustionRadius_positive length lengthPositive index)
      ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive state
      (cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0) point‖ ≤
      cartesianPhysicalBulkConstant parameters length compact M * ‖quotientEta parameters 8 source‖ := by
  let payment := originalSourceAllocationConstant parameters length 0 * (1 + M) * ‖quotientEta parameters 8 source‖
  have paymentNonnegative : 0 ≤ payment :=
    mul_nonneg (mul_nonneg (originalSourceAllocationConstant_positive parameters length 0).le (by positivity)) (norm_nonneg _)
  have inverseNonnegative := independentCoupledDataConstant_nonnegative parameters length compact
  have nativeNonnegative : 0 ≤ 2 * independentCoupledDataConstant parameters length compact * payment := by positivity
  have stateSeven := (physicalBudget_monotone parameters state.val.val.field state.val.val.rho state.val.val.epsilon
    (by norm_num : 7 ≤ 14)).trans stateBound
  have sourceBound := cartesianExhaustionDatum_base_bound parameters length compact lengthPositive widthHalf widthLength
    state small M stateBound source flat vanishing index
  have actual := originalGraphCovariants_fixed_bound parameters length compact (originalExhaustionRadius length index)
    (originalExhaustionRadius_positive length lengthPositive index)
    ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive state
    (cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0) point
    M (2 * independentCoupledDataConstant parameters length compact * payment) payment
    nativeNonnegative paymentNonnegative stateSeven nativeBound sourceBound
  have samePayment : originalReconstructionConstant parameters length compact * (1 + M) *
      ((11 + 4 * length) * (2 * independentCoupledDataConstant parameters length compact * payment) + 3 * payment) =
      cartesianPhysicalBulkConstant parameters length compact M * ‖quotientEta parameters 8 source‖ := by
    dsimp only [payment,cartesianPhysicalBulkConstant]
    ring
  exact actual.trans_eq samePayment

end Grad.ActualPuncturedReconstruction
