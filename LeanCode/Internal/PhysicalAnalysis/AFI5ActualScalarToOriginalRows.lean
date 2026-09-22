import AFI4OriginalBoundaryEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualReferenceAssembly
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearDivision
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.GaugeCoefficients.Envelope
open Grad.ActualScalarForcing Grad.ActualNonexceptionalInverse Grad.RawCircularSectors
open Grad.ActualForcingSupport Grad.BoundedScalarInverse
variable {L sigma gamma ell : ℝ}

theorem originalScalarSolution_excluded (admissible : Admissible L sigma gamma ell)
    (forcing theta : APSmooth L sigma gamma ell 1) (boundary : BandSmoothBoundary L sigma gamma ell)
    (laws : IsOriginalScalarSolution admissible forcing boundary theta) : ScalarAvoidsExceptional admissible theta := by
  intro cell mode exceptional
  rcases exceptional with rfl | rfl | rfl
  · exact (laws cell).1.1
  · exact (laws cell).1.2.1
  · exact (laws cell).1.2.2

theorem originalScalarSolution_equation (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (boundary : BandSmoothBoundary L sigma gamma ell)
    (laws : IsOriginalScalarSolution admissible (scalarForcing admissible source) boundary theta) :
    ActualScalarEquation admissible theta source := by
  intro cell
  have equation := (laws cell).2.1
  rw [fullScalarJet_formula] at equation
  exact (congrArg (fun jet : ClosedJet 1 => -laplacianJet (apSmoothJet admissible 1 cell theta) +
    ((((cell : ℝ) * ell / L) ^ 2 : ℝ) : ℂ) • jet) (apFullB_jet admissible theta cell)).trans equation

/-- The genuine scalar solution, with the actual original forcing, solves
all original interior equations and every grade of the original high boundary. -/
theorem actualScalarSolution_originalRowsAndBoundary (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (compatible : source ∈ smoothCapSourceCore admissible) (sourceExcluded : AvoidsExceptionalSource source)
    (beta : BandSmoothBoundary L sigma gamma ell)
    (laws : IsOriginalScalarSolution admissible (scalarForcing admissible source) (forcedBoundary admissible source beta) theta) :
    AvoidsExceptionalState (reconstructedState admissible theta source) ∧
    circularRows admissible (reconstructedState admissible theta source) = source ∧
    ∀ grade : ℕ, circularCoreTrace admissible grade (reconstructedState admissible theta source) =
      apHighProjection L sigma gamma ell (grade + 1) (beta.grade grade) := by
  have excluded := originalScalarSolution_excluded admissible _ theta _ laws
  exact ⟨Grad.ActualScalarResidual.reconstructedState_excluded admissible theta source excluded sourceExcluded,
    reconstructedState_allInteriorRows admissible theta source compatible excluded sourceExcluded
      (originalScalarSolution_equation admissible theta source _ laws),
    actualScalarSolution_boundary admissible theta source excluded sourceExcluded beta laws⟩

/-- A common original AP state for actual bounded-band source/boundary data;
all equations and every boundary grade are obtained from the same scalar solve. -/
theorem actualForcedOriginalRows (admissible : Admissible L sigma gamma ell)
    (ceiling : ℝ) (parameters : PhaseParameters) (source : SmoothCapSource L sigma gamma ell)
    (compatible : source ∈ smoothCapSourceCore admissible) (sourceExcluded : AvoidsExceptionalSource source)
    (sourceBand : OriginalCapSourceBand admissible ceiling source)
    (beta : BandSmoothBoundary L sigma gamma ell) (betaBand : OriginalBoundaryBand ceiling beta) :
    ∃ theta : APSmooth L sigma gamma ell 1,
      IsOriginalScalarSolution admissible (scalarForcing admissible source) (forcedBoundary admissible source beta) theta ∧
      AvoidsExceptionalState (reconstructedState admissible theta source) ∧
      circularRows admissible (reconstructedState admissible theta source) = source ∧
      ∀ grade : ℕ, circularCoreTrace admissible grade (reconstructedState admissible theta source) =
        apHighProjection L sigma gamma ell (grade + 1) (beta.grade grade) := by
  have conditions := actualForcedScalarInputs admissible ceiling source sourceExcluded sourceBand beta betaBand
  let theta := apBandScalarInverse admissible ceiling parameters (scalarForcing admissible source)
    conditions.1 (forcedBoundary admissible source beta) conditions.2.2.1
  have laws := apBandScalarInverse_specification admissible ceiling parameters _ conditions.1 conditions.2.1
    _ conditions.2.2.1 conditions.2.2.2
  exact ⟨theta, laws, actualScalarSolution_originalRowsAndBoundary admissible theta source compatible sourceExcluded beta laws⟩

end Grad.ActualReferenceAssembly
