import AFU1ActualSectorBandInputs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000
namespace Grad.FullReferenceAssembly
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.GaugeCoefficients.Envelope
open Grad.BoundaryTrace Grad.ActualForcingSupport Grad.BoundedScalarInverse Grad.RawCircularSectors
open Grad.ExceptionalNative Grad.ActualMeanInverse Grad.ActualExceptionalInverse
open Grad.ActualReferenceAssembly Grad.ActualScalarForcing
variable {L sigma gamma ell : ℝ}

/-- The original full reference state is the literal sum of the three
exceptional sector inverses and the actual nonexceptional inverse. -/
def fullReferenceState (admissible : Admissible L sigma gamma ell) (ceiling : ℝ) (parameters : PhaseParameters)
    (source : SmoothCapSource L sigma gamma ell) (beta : BandSmoothBoundary L sigma gamma ell) : CompensatedData L sigma gamma ell :=
  meanInverseLinear L sigma gamma ell (rawSourceProjector L sigma gamma ell 0 source) +
    exceptionalInverseLinear admissible 1 (rawSourceProjector L sigma gamma ell 2 source) +
    exceptionalInverseLinear admissible (-1) (rawSourceProjector L sigma gamma ell (-2) source) +
    actualNonexceptionalState admissible ceiling parameters (rawSourceComplement L sigma gamma ell source)
      (rawSourceComplement_avoids admissible source) beta

private theorem four_map {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (mapping : E →ₗ[ℂ] F) (first second third fourth : E) :
    mapping (first + second + third + fourth) = mapping first + mapping second + mapping third + mapping fourth := by
  rw [map_add, map_add, map_add]

/-- Qualitative full original reference solve on every nonexceptional and
exceptional raw sector together, using the original source and boundary. -/
theorem fullReferenceState_original_equations (admissible : Admissible L sigma gamma ell) (ceiling : ℝ) (parameters : PhaseParameters)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible)
    (band : OriginalCapSourceBand admissible ceiling source) (beta : BandSmoothBoundary L sigma gamma ell)
    (betaBand : OriginalBoundaryBand ceiling beta) (betaHigh : OriginalBoundaryHigh beta) :
    fullReferenceState admissible ceiling parameters source beta ∈ circularCompensatedCore admissible ∧
    circularRows admissible (fullReferenceState admissible ceiling parameters source beta) = source ∧
    ∀ grade : ℕ, 1 ≤ grade → circularCoreTrace admissible grade (fullReferenceState admissible ceiling parameters source beta) = beta.grade grade := by
  let p := rawSourceProjector L sigma gamma ell
  have sourceCore (mode : ℤ) := rawSourceProjector_preserves admissible mode source compatible
  have raw (mode : ℤ) := rawSourceProjector_sector admissible mode source
  have meanRaw := rawSource_zero_mean admissible (p 0 source) (raw 0)
  have positiveRaw : IsRawSourceSector admissible (2 * 1) (p 2 source) := by simpa only [mul_one] using raw 2
  have negativeRaw : IsRawSourceSector admissible (2 * (-1)) (p (-2) source) := by simpa only [mul_neg, mul_one] using raw (-2)
  have rest := actualNonexceptional_original_high_consumer admissible ceiling parameters (rawSourceComplement L sigma gamma ell source)
    (rawSourceComplement_preserves admissible source compatible) (rawSourceComplement_avoids admissible source)
    (rawSourceComplement_band admissible ceiling source band) beta betaBand betaHigh
  constructor
  · exact (circularCompensatedCore admissible).add_mem
      ((circularCompensatedCore admissible).add_mem
        ((circularCompensatedCore admissible).add_mem (meanState_circularCore admissible _ (sourceCore 0) meanRaw)
          (exceptionalState_circularCore admissible 1 (Or.inl rfl) _ positiveRaw))
        (exceptionalState_circularCore admissible (-1) (Or.inr rfl) _ negativeRaw)) rest.1
  constructor
  · exact (four_map (circularRows admissible) _ _ _ _).trans
      ((congrArg₂ (fun a b : SmoothCapSource L sigma gamma ell => a + b)
        (congrArg₂ (fun a b : SmoothCapSource L sigma gamma ell => a + b)
          (congrArg₂ (fun a b : SmoothCapSource L sigma gamma ell => a + b)
            (meanState_rows admissible _ (sourceCore 0) meanRaw)
            (exceptionalState_rows admissible 1 (Or.inl rfl) _ (sourceCore 2) positiveRaw))
          (exceptionalState_rows admissible (-1) (Or.inr rfl) _ (sourceCore (-2)) negativeRaw))
        rest.2.2.1).trans (rawSource_decomposition source))
  · intro grade large
    have mean := meanState_highBoundary admissible _ (sourceCore 0) meanRaw grade large
    have positive := exceptionalState_highBoundary admissible 1 (Or.inl rfl) _ positiveRaw grade large
    have negative := exceptionalState_highBoundary admissible (-1) (Or.inr rfl) _ negativeRaw grade large
    exact (four_map (circularCoreTrace admissible grade) _ _ _ _).trans
      ((congrArg₂ (fun a b : APBoundaryGrade L sigma gamma ell 1 (grade + 1) => a + b)
        (congrArg₂ (fun a b : APBoundaryGrade L sigma gamma ell 1 (grade + 1) => a + b)
          (congrArg₂ (fun a b : APBoundaryGrade L sigma gamma ell 1 (grade + 1) => a + b) mean positive) negative)
        (rest.2.2.2.1 grade)).trans (by simp only [add_zero, zero_add]))

end Grad.FullReferenceAssembly
