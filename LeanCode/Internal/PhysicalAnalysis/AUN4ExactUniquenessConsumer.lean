import AUN3OriginalReconstructionUniqueness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.ActualReconstructionUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Envelope
open Grad.ActualNonexceptionalInverse Grad.RawCircularSectors
variable {L sigma gamma ell : ℝ}

/-- The actual theta/force/third rows distinguish original nonexceptional
circular states. In particular scalar uniqueness suffices for full-state
uniqueness after the original force and third equations have been proved. -/
theorem actualOriginalState_unique (admissible : Admissible L sigma gamma ell)
    (first second : circularCompensatedCore admissible)
    (firstExcluded : AvoidsExceptionalState first.val) (secondExcluded : AvoidsExceptionalState second.val)
    (sameTheta : first.val.1 = second.val.1)
    (sameForce : circularForce admissible first.val = circularForce admissible second.val)
    (sameThird : circularThird admissible first.val = circularThird admissible second.val) : first = second := by
  let source : SmoothCapSource L sigma gamma ell :=
    (circularForce admissible first.val, (0, circularThird admissible first.val))
  apply Subtype.ext
  exact (originalReconstruction_unique admissible first.val.1 source first firstExcluded rfl rfl rfl).trans
    (originalReconstruction_unique admissible first.val.1 source second secondExcluded sameTheta.symm sameForce.symm sameThird.symm).symm

/-- Exact consumer for an arbitrary original circular state, with the actual
ANV formula and the actual original force/third operators. -/
theorem actualOriginalReconstruction_characterization (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (state : circularCompensatedCore admissible) (excluded : AvoidsExceptionalState state.val)
    (sameTheta : state.val.1 = theta) (sameForce : circularForce admissible state.val = source.1)
    (sameThird : circularThird admissible state.val = source.2.2) :
    state.val = (theta, storedPair L sigma gamma ell
      (-apVectorInverse admissible ((2 : ℂ) • apSmoothQuarter L sigma gamma ell (apSmoothGradient admissible theta) + source.1))
      (Grad.ActualAngularInverse.apShiftInverse admissible 0 source.2.2)) :=
  originalReconstruction_unique admissible theta source state excluded sameTheta sameForce sameThird

end Grad.ActualReconstructionUniqueness
