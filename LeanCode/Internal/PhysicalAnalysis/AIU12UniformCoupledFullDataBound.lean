import AIU11CompleteIndependentCoupledData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2000
set_option synthInstance.maxHeartbeats 400000
namespace Grad.AnnularFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse Grad.AnnularCurrentSource
open Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularCrossMaps Grad.AnnularUniformBoundary
open Grad.AnnularCoupledInverse Grad.AnnularKnownLow Grad.AnnularLowEnergy Grad.AnnularCurrentLow
open Grad.GaugeCoefficients.Physical.Allocation

/-- A coefficient fixed before the collar and the background state. -/
def fullKnownHighBallConstant (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  (1 + 8 * eliminatedBulkConstant parameters L compact 0 * (4 + 2 * |L|)) *
    (32 * actualHighKnownBF13BallConstant parameters L compact + 322 * uniformInnerLiftConstant L) +
    32 * eliminatedBulkConstant parameters L compact 0 + 12

theorem fullKnownHighBallConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) :
    0 ≤ fullKnownHighBallConstant parameters L compact := by
  have bulk := eliminatedBulkConstant_nonnegative parameters L compact 0
  have source := actualHighKnownBF13BallConstant_nonnegative parameters L compact
  have lift : 0 ≤ uniformInnerLiftConstant L := Real.sqrt_nonneg _
  unfold fullKnownHighBallConstant
  positivity

theorem fullKnownHighNormConstant_le_ball (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ 1) :
    fullKnownHighNormConstant parameters L compact state ≤ fullKnownHighBallConstant parameters L compact := by
  have sizeBound : state.val.val.size 0 ≤ 2 := by
    have budget := (physicalBudget_monotone parameters state.val.val.field state.val.val.rho state.val.val.epsilon
      (by norm_num : 0 + 7 ≤ 8)).trans small
    change 1 + physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (0 + 7) ≤ 2
    linarith
  have sourceBound := actualHighKnownBF13Constant_le_ball parameters L compact state small
  have bulk := eliminatedBulkConstant_nonnegative parameters L compact 0
  have source := actualHighKnownBF13Constant_nonnegative parameters L compact state
  have lift : 0 ≤ uniformInnerLiftConstant L := Real.sqrt_nonneg _
  unfold fullKnownHighNormConstant fullKnownHighBallConstant
  calc
    _ ≤ (1 + 4 * eliminatedBulkConstant parameters L compact 0 * 2 * (4 + 2 * |L|)) *
        (32 * actualHighKnownBF13BallConstant parameters L compact + 322 * uniformInnerLiftConstant L) +
        16 * eliminatedBulkConstant parameters L compact 0 * 2 + 12 := by gcongr
    _ = _ := by ring

/-- Uniform bound for the two complete independently prescribed data blocks.
The subsequent full strong-data embedding shares its original F0/F2 tuple. -/
def independentCoupledDataConstant (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  2 * (fullKnownHighBallConstant parameters L compact + knownLowResponseConstant parameters L compact)

theorem independentCoupledDataConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) :
    0 ≤ independentCoupledDataConstant parameters L compact := by
  exact mul_nonneg (by norm_num) (add_nonneg (fullKnownHighBallConstant_nonnegative parameters L compact)
    (knownLowResponseConstant_nonnegative parameters L compact))

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters L compact)

theorem independentCoupledResponse_uniform
    (data : IndependentCoupledData parameters lower positive (lowerHalf.trans (by norm_num))) :
    let response : CoupledSpace lower L positive lengthPositive :=
      independentCoupledResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
    ‖response‖ ≤
      independentCoupledDataConstant parameters L compact * ‖data‖ := by
  apply (independentCoupledResponse_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data).trans
  have highBound := fullKnownHighNormConstant_le_ball parameters L compact state
    (coupledPrimitive_budget_one parameters L compact state small)
  unfold independentCoupledDataConstant
  gcongr

end Grad.AnnularFullSource
