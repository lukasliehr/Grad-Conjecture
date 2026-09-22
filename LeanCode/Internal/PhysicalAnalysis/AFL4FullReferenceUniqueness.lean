import AFL3ExceptionalProjectionIdentification

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000
namespace Grad.FullReferenceUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.GaugeCoefficients.Envelope
open Grad.RawCircularSectors Grad.FullReferenceAssembly Grad.BoundedScalarInverse Grad.ActualForcingSupport
open Grad.ActualReferenceAssembly Grad.OriginalNonexceptionalUniqueness
variable {L sigma gamma ell : ℝ}

private theorem subtract_trace {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (mapping : E →ₗ[ℂ] F) (state first second third : E) (target : F)
    (whole : mapping state = target) (one : mapping first = 0) (two : mapping second = 0) (three : mapping third = 0) :
    mapping (state - (first + second + third)) = target := by
  rw [map_sub, map_add, map_add, whole, one, two, three, add_zero, add_zero, sub_zero]

/-- Any original circular state with the specified rows and boundary is the
single full reference state. Its frequency support is not an extra assumption. -/
theorem fullReferenceState_unique (admissible : Admissible L sigma gamma ell)
    (ceiling : ℝ) (parameters : PhaseParameters)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible)
    (band : OriginalCapSourceBand admissible ceiling source)
    (beta : BandSmoothBoundary L sigma gamma ell) (betaBand : OriginalBoundaryBand ceiling beta)
    (state : circularCompensatedCore admissible) (rows : circularRows admissible state.val = source)
    (boundary : circularCoreTrace admissible 1 state.val = beta.grade 1) :
    state.val = fullReferenceState admissible ceiling parameters source beta := by
  let p := rawStateProjector L sigma gamma ell
  have mean := meanProjection_eq admissible source state rows
  have positive : p 2 state.val = Grad.ActualExceptionalInverse.exceptionalInverseLinear admissible 1
      (rawSourceProjector L sigma gamma ell 2 source) := by
    simpa only [mul_one] using exceptionalProjection_eq admissible 1 (Or.inl rfl) source compatible state rows
  have negative : p (-2) state.val = Grad.ActualExceptionalInverse.exceptionalInverseLinear admissible (-1)
      (rawSourceProjector L sigma gamma ell (-2) source) := by
    simpa only [mul_neg, mul_one] using exceptionalProjection_eq admissible (-1) (Or.inr rfl) source compatible state rows
  have positiveTrace : circularCoreTrace admissible 1 (p 2 state.val) = 0 := by
    simpa only [mul_one] using exceptionalProjection_trace_zero admissible 1 (Or.inl rfl) source compatible state rows 1
  have negativeTrace : circularCoreTrace admissible 1 (p (-2) state.val) = 0 := by
    simpa only [mul_neg, mul_one] using exceptionalProjection_trace_zero admissible (-1) (Or.inr rfl) source compatible state rows 1
  let rest : circularCompensatedCore admissible :=
    ⟨rawStateComplement L sigma gamma ell state.val, rawStateComplement_preserves admissible state.val state.property⟩
  have restRows := (circularRows_rawComplement admissible state.val).trans
    (congrArg (rawSourceComplement L sigma gamma ell) rows)
  have restBoundary : circularCoreTrace admissible 1 rest.val = beta.grade 1 :=
    subtract_trace (circularCoreTrace admissible 1) state.val (p 0 state.val) (p 2 state.val) (p (-2) state.val)
      (beta.grade 1) boundary (meanProjection_trace_zero admissible source compatible state rows 1) positiveTrace negativeTrace
  have restUnique := actualNonexceptional_unique admissible ceiling parameters (rawSourceComplement L sigma gamma ell source)
    (rawSourceComplement_avoids admissible source) (rawSourceComplement_band admissible ceiling source band)
    beta betaBand rest (rawStateComplement_avoids admissible state.val) restRows
    (circularTrace_eq_all admissible rest.val beta restBoundary)
  exact (rawState_decomposition state.val).symm.trans
    (congrArg₂ (fun first second : CompensatedData L sigma gamma ell => first + second)
      (congrArg₂ (fun first second : CompensatedData L sigma gamma ell => first + second)
        (congrArg₂ (fun first second : CompensatedData L sigma gamma ell => first + second) mean positive) negative) restUnique)

/-- Full smooth original reference inverse: actual domain, all rows, every
coherent physical boundary grade, original native estimate, and uniqueness. -/
theorem fullReference_inverse_consumer (admissible : Admissible L sigma gamma ell)
    (ceiling : ℝ) (parameters : PhaseParameters)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible)
    (band : OriginalCapSourceBand admissible ceiling source)
    (beta : BandSmoothBoundary L sigma gamma ell) (betaBand : OriginalBoundaryBand ceiling beta)
    (betaHigh : OriginalBoundaryHigh beta) :
    fullReferenceState admissible ceiling parameters source beta ∈ circularCompensatedCore admissible ∧
    circularRows admissible (fullReferenceState admissible ceiling parameters source beta) = source ∧
    (∀ grade : ℕ, circularCoreTrace admissible grade (fullReferenceState admissible ceiling parameters source beta) = beta.grade grade) ∧
    (∀ grade : ℕ, ∀ large : 3 ≤ grade,
      compensatedNorm admissible grade (fullReferenceState admissible ceiling parameters source beta) ≤
        fullReferenceNativeConstant L gamma ceiling grade large * (‖capSourceGrade grade source‖ + ‖beta.grade grade‖)) ∧
    (∀ state : circularCompensatedCore admissible, circularRows admissible state.val = source →
      circularCoreTrace admissible 1 state.val = beta.grade 1 →
      state.val = fullReferenceState admissible ceiling parameters source beta) := by
  have solved := fullReference_right_inverse_consumer admissible ceiling parameters source compatible band beta betaBand betaHigh
  exact ⟨solved.1, solved.2.1, circularTrace_eq_all admissible _ beta (solved.2.2.1 1 (by omega)),
    solved.2.2.2, fullReferenceState_unique admissible ceiling parameters source compatible band beta betaBand⟩

end Grad.FullReferenceUniqueness
