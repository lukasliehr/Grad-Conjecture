import AFI5ActualScalarToOriginalRows
import AUS2OriginalScalarDomainConsumer
import ACF3ActualUniformRadialForcing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualReferenceAssembly
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.GaugeCoefficients.Envelope
open Grad.ActualScalarForcing Grad.ActualNonexceptionalInverse Grad.RawCircularSectors
open Grad.ActualForcingSupport Grad.BoundedScalarInverse Grad.SameCellFixedMultiplication
variable {L sigma gamma ell : ℝ}

/-- The actual scalar solution, chosen once before every Sobolev grade. -/
def actualForcedPotential (admissible : Admissible L sigma gamma ell)
    (ceiling : ℝ) (parameters : PhaseParameters) (source : SmoothCapSource L sigma gamma ell)
    (excluded : AvoidsExceptionalSource source) (beta : BandSmoothBoundary L sigma gamma ell) : APSmooth L sigma gamma ell 1 :=
  apBandScalarInverse admissible ceiling parameters (scalarForcing admissible source)
    (scalarForcing_nonexceptional admissible source excluded) (forcedBoundary admissible source beta)
    (forcedBoundary_high admissible source beta)

theorem actualForcedPotential_laws (admissible : Admissible L sigma gamma ell)
    (ceiling : ℝ) (parameters : PhaseParameters) (source : SmoothCapSource L sigma gamma ell)
    (excluded : AvoidsExceptionalSource source) (sourceBand : OriginalCapSourceBand admissible ceiling source)
    (beta : BandSmoothBoundary L sigma gamma ell) (betaBand : OriginalBoundaryBand ceiling beta) :
    IsOriginalScalarSolution admissible (scalarForcing admissible source) (forcedBoundary admissible source beta)
      (actualForcedPotential admissible ceiling parameters source excluded beta) :=
  apBandScalarInverse_specification admissible ceiling parameters _ (scalarForcing_nonexceptional admissible source excluded)
    (scalarForcing_band admissible ceiling source sourceBand) _ (forcedBoundary_high admissible source beta)
    (forcedBoundary_band admissible ceiling source sourceBand beta betaBand)

/-- One actual original state, independent of the requested grade. -/
def actualNonexceptionalState (admissible : Admissible L sigma gamma ell)
    (ceiling : ℝ) (parameters : PhaseParameters) (source : SmoothCapSource L sigma gamma ell)
    (excluded : AvoidsExceptionalSource source) (beta : BandSmoothBoundary L sigma gamma ell) : CompensatedData L sigma gamma ell :=
  reconstructedState admissible (actualForcedPotential admissible ceiling parameters source excluded beta) source

def nonexceptionalNativeConstant (L gamma ceiling : ℝ) (grade : ℕ) (large : 3 ≤ grade) : ℝ :=
  reconstructionConstant L gamma grade *
    (bandScalarGainConstant L gamma ceiling grade large * (forcingConstant L gamma grade + boundaryResponseConstant grade + 1) + 2)

private theorem source_sum_bound (value theta force third source boundary reconstruction scalar data : ℝ)
    (sourceNonnegative : 0 ≤ source) (boundaryNonnegative : 0 ≤ boundary)
    (reconstructionNonnegative : 0 ≤ reconstruction) (scalarNonnegative : 0 ≤ scalar) (dataNonnegative : 0 ≤ data)
    (estimate : value ≤ reconstruction * (theta + force + third))
    (thetaBound : theta ≤ scalar * (data * source + boundary)) (forceBound : force ≤ source) (thirdBound : third ≤ source) :
    value ≤ reconstruction * (scalar * (data + 1) + 2) * (source + boundary) := by
  have dataBound : data * source + boundary ≤ (data + 1) * (source + boundary) := by
    nlinarith [mul_nonneg dataNonnegative boundaryNonnegative]
  have thetaPaid := thetaBound.trans (mul_le_mul_of_nonneg_left dataBound scalarNonnegative)
  have total : theta + force + third ≤ (scalar * (data + 1) + 2) * (source + boundary) := by
    have lower : source ≤ source + boundary := le_add_of_nonneg_right boundaryNonnegative
    have combined := add_le_add (add_le_add thetaPaid (forceBound.trans lower)) (thirdBound.trans lower)
    exact combined.trans_eq (by ring)
  exact estimate.trans ((mul_le_mul_of_nonneg_left total reconstructionNonnegative).trans_eq (mul_assoc _ _ _).symm)

/-- Native AN33 estimate for the actual nonexceptional state at the original
width, with its constant independent of sigma, ell, and the source. -/
theorem actualNonexceptional_native_bound (admissible : Admissible L sigma gamma ell)
    (ceiling : ℝ) (parameters : PhaseParameters) (source : SmoothCapSource L sigma gamma ell)
    (compatible : source ∈ smoothCapSourceCore admissible) (excluded : AvoidsExceptionalSource source)
    (sourceBand : OriginalCapSourceBand admissible ceiling source)
    (beta : BandSmoothBoundary L sigma gamma ell) (betaBand : OriginalBoundaryBand ceiling beta)
    (grade : ℕ) (large : 3 ≤ grade) :
    compensatedNorm admissible grade (actualNonexceptionalState admissible ceiling parameters source excluded beta) ≤
      nonexceptionalNativeConstant L gamma ceiling grade large * (‖capSourceGrade grade source‖ + ‖beta.grade grade‖) := by
  let theta := actualForcedPotential admissible ceiling parameters source excluded beta
  have laws := actualForcedPotential_laws admissible ceiling parameters source excluded sourceBand beta betaBand
  have thetaExcluded := originalScalarSolution_excluded admissible _ theta _ laws
  have stateBound := reconstructedState_native_bound admissible theta source compatible
    (reconstructionLoad_nonresonant admissible theta source thetaExcluded excluded) grade
  have scalarBound := apBandScalarInverse_native_gain admissible ceiling parameters _
    (scalarForcing_nonexceptional admissible source excluded) _ (forcedBoundary_high admissible source beta) grade large
  have dataBound := actualScalarForcing_uniform_width admissible grade source (beta.grade grade)
  have thetaBound := scalarBound.trans (mul_le_mul_of_nonneg_left dataBound
    (bandScalarGainConstant_nonnegative L gamma ceiling (admissible_gamma_nonnegative admissible) grade large))
  exact source_sum_bound _ _ _ _ _ _ _ _ _ (norm_nonneg _) (norm_nonneg _)
    (reconstructionConstant_nonnegative admissible grade)
    (bandScalarGainConstant_nonnegative L gamma ceiling (admissible_gamma_nonnegative admissible) grade large)
    (add_nonneg (forcingConstant_nonnegative admissible grade) (boundaryResponseConstant_nonnegative grade))
    stateBound thetaBound (capSource_components_bound grade source).1 (capSource_components_bound grade source).2.2

/-- Actual bounded-band nonexceptional reference inverse existence: one
original-domain state, every original interior/boundary equation, and the sharp
five-slot native bound at every s >= 3. Full-state uniqueness is a later block. -/
theorem actualNonexceptional_reference_consumer (admissible : Admissible L sigma gamma ell)
    (ceiling : ℝ) (parameters : PhaseParameters) (source : SmoothCapSource L sigma gamma ell)
    (compatible : source ∈ smoothCapSourceCore admissible) (excluded : AvoidsExceptionalSource source)
    (sourceBand : OriginalCapSourceBand admissible ceiling source)
    (beta : BandSmoothBoundary L sigma gamma ell) (betaBand : OriginalBoundaryBand ceiling beta) :
    let state := actualNonexceptionalState admissible ceiling parameters source excluded beta
    state ∈ circularCompensatedCore admissible ∧ AvoidsExceptionalState state ∧ circularRows admissible state = source ∧
    (∀ grade : ℕ, circularCoreTrace admissible grade state = apHighProjection L sigma gamma ell (grade + 1) (beta.grade grade)) ∧
    (∀ (grade : ℕ) (large : 3 ≤ grade), compensatedNorm admissible grade state ≤
      nonexceptionalNativeConstant L gamma ceiling grade large * (‖capSourceGrade grade source‖ + ‖beta.grade grade‖)) := by
  let theta := actualForcedPotential admissible ceiling parameters source excluded beta
  have laws := actualForcedPotential_laws admissible ceiling parameters source excluded sourceBand beta betaBand
  have thetaExcluded := originalScalarSolution_excluded admissible _ theta _ laws
  have thetaFlat := Grad.ActualScalarAxis.originalScalarSolution_firstJet admissible _ _ theta laws
  have rows := actualScalarSolution_originalRowsAndBoundary admissible theta source compatible excluded beta laws
  exact ⟨reconstructedState_circularCore admissible theta source compatible thetaExcluded excluded thetaFlat,
    rows.1, rows.2.1, rows.2.2,
    actualNonexceptional_native_bound admissible ceiling parameters source compatible excluded sourceBand beta betaBand⟩

theorem originalBoundaryHigh_projection (beta : BandSmoothBoundary L sigma gamma ell)
    (high : OriginalBoundaryHigh beta) (grade : ℕ) :
    apHighProjection L sigma gamma ell (grade + 1) (beta.grade grade) = beta.grade grade := by
  apply originalBoundary_ext (grade + 1)
  intro pair
  have projected := apHighProjection_coefficient L sigma gamma ell (grade + 1) (beta.grade grade) pair
  by_cases large : 3 ≤ |pair.1|
  · exact projected.trans (if_pos large)
  · have zero := (beta.coherent grade pair).trans (high pair.1 (not_highMode_low pair.1 large) pair.2)
    exact projected.trans ((if_neg large).trans zero.symm)

/-- Exact high-boundary-data endpoint on the paper's original domain and
norms. Every grade is solved by the same actual state. -/
theorem actualNonexceptional_original_high_consumer (admissible : Admissible L sigma gamma ell)
    (ceiling : ℝ) (parameters : PhaseParameters) (source : SmoothCapSource L sigma gamma ell)
    (compatible : source ∈ smoothCapSourceCore admissible) (excluded : AvoidsExceptionalSource source)
    (sourceBand : OriginalCapSourceBand admissible ceiling source)
    (beta : BandSmoothBoundary L sigma gamma ell) (betaBand : OriginalBoundaryBand ceiling beta)
    (betaHigh : OriginalBoundaryHigh beta) :
    let state := actualNonexceptionalState admissible ceiling parameters source excluded beta
    state ∈ circularCompensatedCore admissible ∧ AvoidsExceptionalState state ∧ circularRows admissible state = source ∧
    (∀ grade : ℕ, circularCoreTrace admissible grade state = beta.grade grade) ∧
    (∀ (grade : ℕ) (large : 3 ≤ grade), compensatedNorm admissible grade state ≤
      nonexceptionalNativeConstant L gamma ceiling grade large * (‖capSourceGrade grade source‖ + ‖beta.grade grade‖)) := by
  have original := actualNonexceptional_reference_consumer admissible ceiling parameters source compatible excluded sourceBand beta betaBand
  exact ⟨original.1, original.2.1, original.2.2.1,
    fun grade => (original.2.2.2.1 grade).trans (originalBoundaryHigh_projection beta betaHigh grade), original.2.2.2.2⟩

end Grad.ActualReferenceAssembly
