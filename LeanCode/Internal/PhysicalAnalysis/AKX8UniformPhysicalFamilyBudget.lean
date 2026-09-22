import AKX7ActualCovariantFamilies

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


def originalReconstructionConstant (parameters : PhaseParameters) (length compact : ℝ) : ℝ :=
  (originalGraphCovariants_uniform parameters length compact).choose

theorem originalReconstructionConstant_nonnegative (parameters : PhaseParameters) (length compact : ℝ) :
    0 ≤ originalReconstructionConstant parameters length compact :=
  (originalGraphCovariants_uniform parameters length compact).choose_spec.1

/-- The same reconstruction constant works for every collar, with the
original weighted retained and source norms. -/
theorem originalGraphCovariants_fixed_bound (parameters : PhaseParameters) (length compact : ℝ)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (data : OriginalStrongCarrier parameters lower 0 0)
    (point : OriginalFiveBlockAmbient parameters lower length positive)
    (M native source : ℝ) (nativeNonnegative : 0 ≤ native) (sourceNonnegative : 0 ≤ source)
    (stateBound : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 7 ≤ M)
    (nativeBound : originalWeightedRetainedNorm parameters lower length positive bounded lengthPositive point.ofLp.1 ≤ native)
    (sourceBound : originalWeightedDatumNorm parameters lower length positive bounded lengthPositive data ≤ source) :
    ‖originalGraphCovariant parameters length compact lower positive bounded lengthPositive state data point‖ +
      ‖originalGraphRotatedCovariant parameters length compact lower positive bounded lengthPositive state data point‖ ≤
      originalReconstructionConstant parameters length compact * (1 + M) * ((11 + 4 * length) * native + 3 * source) := by
  have initial := (originalGraphCovariants_uniform parameters length compact).choose_spec.2
    lower positive bounded lengthPositive state data point
  have budgetNonnegative := physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon 7
  have leftNonnegative : 0 ≤ originalReconstructionConstant parameters length compact *
      (1 + physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 7) :=
    mul_nonneg (originalReconstructionConstant_nonnegative parameters length compact)
      (by positivity)
  have paymentBound :
      (11 + 4 * length) * originalWeightedRetainedNorm parameters lower length positive bounded lengthPositive point.ofLp.1 +
        3 * originalWeightedDatumNorm parameters lower length positive bounded lengthPositive data ≤
      (11 + 4 * length) * native + 3 * source :=
    add_le_add (mul_le_mul_of_nonneg_left nativeBound (by positivity)) (mul_le_mul_of_nonneg_left sourceBound (by norm_num))
  have leftBound : originalReconstructionConstant parameters length compact *
      (1 + physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 7) ≤
      originalReconstructionConstant parameters length compact * (1 + M) :=
    mul_le_mul_of_nonneg_left (add_le_add le_rfl stateBound) (originalReconstructionConstant_nonnegative parameters length compact)
  exact initial.trans ((mul_le_mul_of_nonneg_left paymentBound leftNonnegative).trans
    (mul_le_mul_of_nonneg_right leftBound (by positivity)))

end Grad.ActualPuncturedReconstruction
