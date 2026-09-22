import AFT3OriginalScalarLaws

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.OriginalNonexceptionalUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.GaugeCoefficients.Envelope
open Grad.ActualScalarForcing Grad.ActualNonexceptionalInverse
open Grad.ActualReferenceAssembly Grad.ActualForcingSupport Grad.RawCircularSectors Grad.BoundedScalarInverse
variable {L sigma gamma ell : ℝ}

/-- Full original-state uniqueness follows from the derived scalar laws and
the accepted scalar inverse, with no scalar equation assumed of the candidate. -/
theorem actualNonexceptional_unique (admissible : Admissible L sigma gamma ell)
    (ceiling : ℝ) (parameters : PhaseParameters) (source : SmoothCapSource L sigma gamma ell)
    (sourceExcluded : AvoidsExceptionalSource source) (sourceBand : OriginalCapSourceBand admissible ceiling source)
    (beta : BandSmoothBoundary L sigma gamma ell) (betaBand : OriginalBoundaryBand ceiling beta)
    (state : circularCompensatedCore admissible) (excluded : AvoidsExceptionalState state.val)
    (rows : circularRows admissible state.val = source)
    (boundary : ∀ grade : ℕ, circularCoreTrace admissible grade state.val = beta.grade grade) :
    state.val = actualNonexceptionalState admissible ceiling parameters source sourceExcluded beta := by
  have laws := originalState_scalar_laws admissible state excluded source sourceExcluded rows beta boundary
  have sameTheta : state.val.1 = actualForcedPotential admissible ceiling parameters source sourceExcluded beta :=
    apBandScalarInverse_unique admissible ceiling parameters _ (scalarForcing_nonexceptional admissible source sourceExcluded)
      (scalarForcing_band admissible ceiling source sourceBand) _ (forcedBoundary_high admissible source beta)
      (forcedBoundary_band admissible ceiling source sourceBand beta betaBand) state.val.1 laws
  exact (originalRows_reconstruction admissible state excluded source rows).trans
    (congrArg (fun theta => reconstructedState admissible theta source) sameTheta)

/-- The same grade-independent actual nonexceptional inverse has original
domain membership, all original equations, the native estimate, and uniqueness
among arbitrary original-domain nonexceptional states with those data. -/
theorem actualNonexceptional_inverse_consumer (admissible : Admissible L sigma gamma ell)
    (ceiling : ℝ) (parameters : PhaseParameters) (source : SmoothCapSource L sigma gamma ell)
    (compatible : source ∈ smoothCapSourceCore admissible) (sourceExcluded : AvoidsExceptionalSource source)
    (sourceBand : OriginalCapSourceBand admissible ceiling source)
    (beta : BandSmoothBoundary L sigma gamma ell) (betaBand : OriginalBoundaryBand ceiling beta)
    (betaHigh : OriginalBoundaryHigh beta) :
    let state := actualNonexceptionalState admissible ceiling parameters source sourceExcluded beta
    state ∈ circularCompensatedCore admissible ∧ AvoidsExceptionalState state ∧ circularRows admissible state = source ∧
    (∀ grade : ℕ, circularCoreTrace admissible grade state = beta.grade grade) ∧
    (∀ (grade : ℕ) (large : 3 ≤ grade), compensatedNorm admissible grade state ≤
      nonexceptionalNativeConstant L gamma ceiling grade large * (‖capSourceGrade grade source‖ + ‖beta.grade grade‖)) ∧
    (∀ candidate : circularCompensatedCore admissible, AvoidsExceptionalState candidate.val →
      circularRows admissible candidate.val = source →
      (∀ grade : ℕ, circularCoreTrace admissible grade candidate.val = beta.grade grade) → candidate.val = state) := by
  have original := actualNonexceptional_original_high_consumer admissible ceiling parameters source compatible sourceExcluded sourceBand beta betaBand betaHigh
  exact ⟨original.1, original.2.1, original.2.2.1, original.2.2.2.1, original.2.2.2.2,
    actualNonexceptional_unique admissible ceiling parameters source sourceExcluded sourceBand beta betaBand⟩

end Grad.OriginalNonexceptionalUniqueness
