import AFU3FullNativeBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.FullReferenceAssembly
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.GaugeCoefficients.Envelope
open Grad.ActualForcingSupport Grad.BoundedScalarInverse
variable {L sigma gamma ell : ℝ}

/-- The single full reference state solves the original circular problem and
satisfies every native estimate at the original analytic width. -/
theorem fullReference_right_inverse_consumer (admissible : Admissible L sigma gamma ell)
    (ceiling : ℝ) (parameters : PhaseParameters)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible)
    (band : OriginalCapSourceBand admissible ceiling source) (beta : BandSmoothBoundary L sigma gamma ell)
    (betaBand : OriginalBoundaryBand ceiling beta) (betaHigh : OriginalBoundaryHigh beta) :
    fullReferenceState admissible ceiling parameters source beta ∈ circularCompensatedCore admissible ∧
    circularRows admissible (fullReferenceState admissible ceiling parameters source beta) = source ∧
    (∀ grade : ℕ, 1 ≤ grade → circularCoreTrace admissible grade (fullReferenceState admissible ceiling parameters source beta) = beta.grade grade) ∧
    (∀ grade : ℕ, ∀ large : 3 ≤ grade,
      compensatedNorm admissible grade (fullReferenceState admissible ceiling parameters source beta) ≤
        fullReferenceNativeConstant L gamma ceiling grade large * (‖capSourceGrade grade source‖ + ‖beta.grade grade‖)) := by
  have equations := fullReferenceState_original_equations admissible ceiling parameters source compatible band beta betaBand betaHigh
  exact ⟨equations.1, equations.2.1, equations.2.2,
    fun grade large => fullReferenceState_native_bound admissible ceiling parameters source compatible band beta betaBand grade large⟩

end Grad.FullReferenceAssembly
