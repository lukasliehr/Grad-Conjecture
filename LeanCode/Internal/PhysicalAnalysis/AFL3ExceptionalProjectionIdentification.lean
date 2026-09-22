import AFL2OriginalTraceCoherence
import AFU4FullReferenceRightInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000
namespace Grad.FullReferenceUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.GaugeCoefficients.Envelope
open Grad.RawCircularSectors Grad.ActualMeanInverse Grad.ActualExceptionalInverse Grad.FullReferenceAssembly
variable {L sigma gamma ell : ℝ}

theorem rawState_zero_mean (admissible : Admissible L sigma gamma ell)
    (state : CompensatedData L sigma gamma ell) (raw : IsRawStateSector admissible 0 state) :
    IsRawMeanState admissible state :=
  ⟨raw.1, fun cell => (rawVectorJet_zero _).symm.trans (raw.2.1 cell), raw.2.2⟩

theorem meanProjection_eq (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (state : circularCompensatedCore admissible)
    (rows : circularRows admissible state.val = source) :
    rawStateProjector L sigma gamma ell 0 state.val =
      meanInverseLinear L sigma gamma ell (rawSourceProjector L sigma gamma ell 0 source) := by
  let projected : circularCompensatedCore admissible :=
    ⟨rawStateProjector L sigma gamma ell 0 state.val, rawStateProjector_preserves admissible 0 state.val state.property⟩
  have actual := (circularRows_rawState admissible 0 state.val).trans
    (congrArg (rawSourceProjector L sigma gamma ell 0) rows)
  exact meanState_unique admissible _ projected
    (rawState_zero_mean admissible _ (rawStateProjector_sector admissible 0 state.val)) (congrArg Prod.fst actual)

theorem exceptionalProjection_eq (admissible : Admissible L sigma gamma ell)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible)
    (state : circularCompensatedCore admissible) (rows : circularRows admissible state.val = source) :
    rawStateProjector L sigma gamma ell (2 * sign) state.val =
      exceptionalInverseLinear admissible sign (rawSourceProjector L sigma gamma ell (2 * sign) source) := by
  have sourceRaw := rawSourceProjector_sector admissible (2 * sign) source
  have actual := (circularRows_rawState admissible (2 * sign) state.val).trans
    (congrArg (rawSourceProjector L sigma gamma ell (2 * sign)) rows)
  exact exceptionalState_sameRows_unique admissible sign signed _ _
    (rawStateProjector_preserves admissible (2 * sign) state.val state.property)
    (exceptionalState_circularCore admissible sign signed _ sourceRaw)
    (rawStateProjector_sector admissible (2 * sign) state.val)
    (exceptionalState_sector admissible sign signed _ sourceRaw)
    (actual.trans (exceptionalState_rows admissible sign signed _
      (rawSourceProjector_preserves admissible (2 * sign) source compatible) sourceRaw).symm)

theorem meanProjection_trace_zero (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible)
    (state : circularCompensatedCore admissible) (rows : circularRows admissible state.val = source) (grade : ℕ) :
    circularCoreTrace admissible grade (rawStateProjector L sigma gamma ell 0 state.val) = 0 := by
  apply circularTrace_zero_all admissible _ _ grade
  exact (congrArg (circularCoreTrace admissible 1) (meanProjection_eq admissible source state rows)).trans
    (meanState_highBoundary admissible _ (rawSourceProjector_preserves admissible 0 source compatible)
      (rawSource_zero_mean admissible _ (rawSourceProjector_sector admissible 0 source)) 1 (by omega))

theorem exceptionalProjection_trace_zero (admissible : Admissible L sigma gamma ell)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible)
    (state : circularCompensatedCore admissible) (rows : circularRows admissible state.val = source) (grade : ℕ) :
    circularCoreTrace admissible grade (rawStateProjector L sigma gamma ell (2 * sign) state.val) = 0 := by
  have identifies := (exceptionalProjection_eq admissible sign signed source compatible state rows).trans
    (exceptionalInverseLinear_apply admissible sign (rawSourceProjector L sigma gamma ell (2 * sign) source))
  have traceOne := (congrArg (circularCoreTrace admissible 1) identifies).trans
    (exceptionalState_highBoundary admissible sign signed (rawSourceProjector L sigma gamma ell (2 * sign) source)
      (rawSourceProjector_sector admissible (2 * sign) source) 1 (by omega))
  exact circularTrace_zero_all admissible _ traceOne grade

end Grad.FullReferenceUniqueness
