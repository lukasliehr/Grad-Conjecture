import AUS1ActualScalarAxis

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.ActualScalarAxis
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearDivision
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Envelope
open Grad.ActualCenterVolterra Grad.RawCircularSectors Grad.BoundedScalarInverse Grad.ActualNonexceptionalInverse
variable {L sigma gamma ell : ℝ}

theorem originalScalarSolution_firstJet (admissible : Admissible L sigma gamma ell)
    (source : APSmooth L sigma gamma ell 1) (boundary : BandSmoothBoundary L sigma gamma ell)
    (solution : APSmooth L sigma gamma ell 1) (laws : IsOriginalScalarSolution admissible source boundary solution) :
    APSmoothAxisFirstJetZero admissible solution := by
  apply apSmoothAxisFirstJetZero_of_closed admissible
  intro cell
  exact scalar_firstJet_of_center_pins _ (laws cell).1.1 (laws cell).2.2.1

theorem originalScalarSolution_excluded (admissible : Admissible L sigma gamma ell)
    (source : APSmooth L sigma gamma ell 1) (boundary : BandSmoothBoundary L sigma gamma ell)
    (solution : APSmooth L sigma gamma ell 1) (laws : IsOriginalScalarSolution admissible source boundary solution) :
    ScalarAvoidsExceptional admissible solution := by
  intro cell mode exceptional
  rcases exceptional with rfl | rfl | rfl
  · exact (laws cell).1.1
  · exact (laws cell).1.2.1
  · exact (laws cell).1.2.2

/-- Exact theta conditions needed by ANV's original-domain reconstruction,
now derived from the SAME actual scalar inverse and its proved laws. -/
theorem actualBandScalar_reconstruction_conditions (admissible : Admissible L sigma gamma ell)
    (ceiling : ℝ) (parameters : PhaseParameters) (source : APSmooth L sigma gamma ell 1)
    (excluded : OriginalSourceNonexceptional admissible source) (sourceBand : OriginalSourceBand admissible ceiling source)
    (boundary : BandSmoothBoundary L sigma gamma ell) (high : OriginalBoundaryHigh boundary)
    (boundaryBand : OriginalBoundaryBand ceiling boundary) :
    let solution := apBandScalarInverse admissible ceiling parameters source excluded boundary high
    ScalarAvoidsExceptional admissible solution ∧ APSmoothAxisFirstJetZero admissible solution := by
  have laws := apBandScalarInverse_specification admissible ceiling parameters source excluded sourceBand boundary high boundaryBand
  exact ⟨originalScalarSolution_excluded admissible source boundary _ laws,
    originalScalarSolution_firstJet admissible source boundary _ laws⟩

/-- Conversely, an arbitrary original circular nonexceptional state's theta
has precisely the scalar exclusions and center pins used in ANB uniqueness. -/
theorem originalCircularState_scalar_conditions (admissible : Admissible L sigma gamma ell)
    (state : circularCompensatedCore admissible) (excluded : AvoidsExceptionalState state.val) :
    ScalarAvoidsExceptional admissible state.val.1 ∧
      ∀ (cell mode : ℤ), mode = 1 ∨ mode = -1 → CenterPinned (angularClosedJet mode (apSmoothJet admissible 1 cell state.val.1)) := by
  constructor
  · intro cell mode exceptional
    exact (rawState_excluded_components admissible mode state.val (excluded mode exceptional) cell).1
  · intro cell mode _
    have flat := ((mem_compensatedFlatCore admissible state.val).mp state.property.1).1.2
    exact center_pins_of_firstJet _ (apSmoothAxisFirstJetZero_closed admissible state.val.1 flat cell) mode

end Grad.ActualScalarAxis
