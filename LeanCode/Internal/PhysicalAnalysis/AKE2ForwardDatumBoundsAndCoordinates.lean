import AKE1OriginalFiveBlockForwardMap

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
namespace Grad.AnnularForwardDatum
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.SourceCollarDivision Grad.AnnularSourceGraph Grad.AnnularCurrentSource
open Grad.AnnularForwardTraces Grad.AnnularStrongOrbit Grad.AnnularLowEnergy
open Grad.ActualBoundaryPrimitives Grad.AnnularVariational Grad.AnnularReconstruction
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)

theorem forwardTraceInput_bound (input : ForwardFiveBlocks parameters lower length positive) :
    ‖forwardTraceInput parameters length lower positive input‖ ≤ ‖input‖ := by
  change max ‖input.ofLp.1‖ ‖input.ofLp.2.ofLp.1‖ ≤ ‖input‖
  exact max_le (hilbert_first_bound input)
    ((hilbert_first_bound input.ofLp.2).trans (hilbert_second_bound input))

/-- An explicit finite bound in the original five-block Hilbert norm. It
is a fixed-positive-collar bound; no radius-uniform estimate is asserted. -/
def originalForwardDatumConstant : ℝ :=
  1 + originalBoundaryTraceConstant parameters length compact lower positive lowerHalf lengthPositive state

theorem originalForwardDatumConstant_nonnegative :
    0 ≤ originalForwardDatumConstant parameters length compact lower positive lowerHalf lengthPositive state :=
  add_nonneg zero_le_one (originalBoundaryTraceConstant_nonnegative parameters length compact lower positive lowerHalf lengthPositive state)

theorem originalForwardAmbient_bound (input : ForwardFiveBlocks parameters lower length positive) :
    ‖originalForwardAmbient parameters length compact lower positive lowerHalf lengthPositive state input‖ ≤
      originalForwardDatumConstant parameters length compact lower positive lowerHalf lengthPositive state * ‖input‖ := by
  have ambient := hilbert_norm_le_add (originalForwardAmbient parameters length compact lower positive lowerHalf lengthPositive state input)
  have source := hilbert_second_bound input
  have boundary := originalBoundaryTrace_bound parameters length compact lower positive lowerHalf lengthPositive state
    (forwardTraceInput parameters length lower positive input)
  have inputBound := forwardTraceInput_bound parameters length lower positive input
  have total := boundary.trans (mul_le_mul_of_nonneg_left inputBound
    (originalBoundaryTraceConstant_nonnegative parameters length compact lower positive lowerHalf lengthPositive state))
  change ‖originalForwardAmbient parameters length compact lower positive lowerHalf lengthPositive state input‖ ≤
    ‖input.ofLp.2‖ + ‖originalBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state
      (forwardTraceInput parameters length lower positive input)‖ at ambient
  unfold originalForwardDatumConstant
  nlinarith only [ambient,source,total]

theorem originalForwardDatum_bound (input : ForwardFiveBlocks parameters lower length positive) :
    ‖originalForwardDatum parameters length compact lower positive lowerHalf lengthPositive state input‖ ≤
      originalForwardDatumConstant parameters length compact lower positive lowerHalf lengthPositive state * ‖input‖ := by
  have contraction := (originalMeanFreeContraction parameters lower).bound
    (originalForwardAmbient parameters length compact lower positive lowerHalf lengthPositive state input)
  exact contraction.trans
    (originalForwardAmbient_bound parameters length compact lower positive lowerHalf lengthPositive state input)

theorem originalForwardDatum_continuous :
    Continuous (originalForwardDatum parameters length compact lower positive lowerHalf lengthPositive state) :=
  (originalForwardDatum parameters length compact lower positive lowerHalf lengthPositive state).continuous

/-- The full original F0 graph is copied with no angular support projection. -/
theorem originalForwardDatum_F0 (input : ForwardFiveBlocks parameters lower length positive) :
    (originalForwardDatum parameters length compact lower positive lowerHalf lengthPositive state input).val.ofLp.1.ofLp.1.ofLp.1 =
      input.ofLp.2.ofLp.1.ofLp.1 := rfl

theorem originalForwardDatum_F2 (input : ForwardFiveBlocks parameters lower length positive) :
    (originalForwardDatum parameters length compact lower positive lowerHalf lengthPositive state input).val.ofLp.1.ofLp.1.ofLp.2 =
      sourceMeanFreeLp input.ofLp.2.ofLp.1.ofLp.2 := rfl

theorem originalForwardDatum_F1 (input : ForwardFiveBlocks parameters lower length positive) :
    (originalForwardDatum parameters length compact lower positive lowerHalf lengthPositive state input).val.ofLp.1.ofLp.2.ofLp.1 =
      sourceMeanFreeLp input.ofLp.2.ofLp.2.ofLp.1 := rfl

theorem originalForwardDatum_G3 (input : ForwardFiveBlocks parameters lower length positive) :
    (originalForwardDatum parameters length compact lower positive lowerHalf lengthPositive state input).val.ofLp.1.ofLp.2.ofLp.2 =
      sourceMeanFreeLp input.ofLp.2.ofLp.2.ofLp.2 := rfl

theorem originalForwardDatum_boundary (input : ForwardFiveBlocks parameters lower length positive) :
    (originalForwardDatum parameters length compact lower positive lowerHalf lengthPositive state input).val.ofLp.2 =
      originalBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state
        (input.ofLp.1,input.ofLp.2.ofLp.1) := rfl

end Grad.AnnularForwardDatum
