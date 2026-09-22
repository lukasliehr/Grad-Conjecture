import AIU9OriginalCoupledWeakRows
import AIS5SingleHilbertNormBF13

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2000
set_option synthInstance.maxHeartbeats 400000
namespace Grad.AnnularFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse Grad.AnnularCurrentSource
open Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularCrossMaps Grad.AnnularUniformBoundary
open Grad.AnnularCurrentGreen Grad.AnnularOmegaGraph Grad.AnnularPhysicalSolution Grad.AnnularCurrentBoundary

/-- The complete high response coefficient in the original independent
source graph and weighted bulk norm. -/
def fullKnownHighNormConstant (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) : ℝ :=
  (1 + 4 * eliminatedBulkConstant parameters L compact 0 * state.val.val.size 0 * (4 + 2 * |L|)) *
    (32 * actualHighKnownBF13Constant parameters L compact state + 322 * uniformInnerLiftConstant L) +
    16 * eliminatedBulkConstant parameters L compact 0 * state.val.val.size 0 + 12

theorem fullKnownHighNormConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) :
    0 ≤ fullKnownHighNormConstant parameters L compact state := by
  have := eliminatedBulkConstant_nonnegative parameters L compact 0
  have := state.val.val.size_nonnegative 0
  have := actualHighKnownBF13Constant_nonnegative parameters L compact state
  have : 0 ≤ uniformInnerLiftConstant L := Real.sqrt_nonneg _
  unfold fullKnownHighNormConstant
  positivity

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)

/-- Exact full high BF15 bound on the literal complete original BF2 data. -/
theorem fullKnownHighResponse_singleNorm
    (data : ActualHighKnownCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0) :
    ‖fullKnownHighResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      (ActualHighKnownCarrier.toGraphKnownData parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data)‖ ≤
      fullKnownHighNormConstant parameters L compact state * ‖data‖ := by
  let known := ActualHighKnownCarrier.toGraphKnownData parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data
  have source : known.functionalSize parameters L compact lower state 0 0 ≤
      actualHighKnownBF13Constant parameters L compact state * ‖data‖ :=
    ActualHighKnownCarrier.functionalSize_le_single_norm parameters L compact lower positive lowerHalf state data
  obtain ⟨weighted, auxiliary, _, _, _, incoming⟩ :=
    ActualHighKnownCarrier.component_bounds parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data
  change ‖known.weighted‖ ≤ ‖data‖ at weighted
  change ‖known.auxiliary‖ ≤ ‖data‖ at auxiliary
  change ‖known.innerValue‖ ≤ ‖data‖ at incoming
  have bulkNonnegative := eliminatedBulkConstant_nonnegative parameters L compact 0
  have stateNonnegative := state.val.val.size_nonnegative 0
  have liftNonnegative : 0 ≤ uniformInnerLiftConstant L := Real.sqrt_nonneg _
  apply (fullKnownHighResponse_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small known).trans
  calc
    _ ≤ (1 + 4 * eliminatedBulkConstant parameters L compact 0 * state.val.val.size 0 * (4 + 2 * |L|)) *
        (32 * (actualHighKnownBF13Constant parameters L compact state * ‖data‖) + 322 * uniformInnerLiftConstant L * ‖data‖) +
        16 * eliminatedBulkConstant parameters L compact 0 * state.val.val.size 0 * ‖data‖ + 12 * ‖data‖ := by
      gcongr
    _ = fullKnownHighNormConstant parameters L compact state * ‖data‖ := by
      unfold fullKnownHighNormConstant
      ring

end Grad.AnnularFullSource
