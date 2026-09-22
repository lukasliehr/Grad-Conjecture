import ANU3ActualCellBand

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualForcingSupport
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.BoundaryTrace Grad.CircularHighWeak
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.ActualScalarForcing Grad.BoundedScalarInverse
variable {L sigma gamma ell : ℝ}

/-- The exact original AN16 boundary datum, common to every Sobolev grade. -/
def forcedBoundary (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (beta : BandSmoothBoundary L sigma gamma ell) :
    BandSmoothBoundary L sigma gamma ell where
  grade order := boundaryForcing admissible order source (beta.grade order)
  coherent order pair := boundaryForcing_coherent admissible order 0 source (beta.grade order) (beta.grade 0)
    (beta.coherent order) pair

theorem forcedBoundary_grade (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (beta : BandSmoothBoundary L sigma gamma ell) (order : ℕ) :
    (forcedBoundary admissible source beta).grade order = boundaryForcing admissible order source (beta.grade order) := rfl

theorem forcedBoundary_coefficient (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (beta : BandSmoothBoundary L sigma gamma ell) (order : ℕ) (pair : ℤ × ℤ) :
    apBoundaryCoefficient L sigma gamma ell (order + 1) ((forcedBoundary admissible source beta).grade order) pair =
      (highMultiplier pair.1 : ℂ) •
        (apBoundaryCoefficient L sigma gamma ell (order + 1) (beta.grade order) pair -
          (angularClosedJet pair.1 (apSmoothJet admissible 1 pair.2 (forceRadial admissible source.1))).value (boundaryDiskPoint 0)) :=
  boundaryForcing_literal_coefficient admissible order source (beta.grade order) pair

theorem forcedBoundary_high (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (beta : BandSmoothBoundary L sigma gamma ell) :
    OriginalBoundaryHigh (forcedBoundary admissible source beta) := by
  intro mode low cell
  rw [forcedBoundary_coefficient, highMultiplier, if_pos low]
  simp only [Complex.ofReal_zero, zero_smul]

theorem forcedBoundary_band (admissible : Admissible L sigma gamma ell)
    (ceiling : ℝ) (source : SmoothCapSource L sigma gamma ell) (sourceBand : OriginalCapSourceBand admissible ceiling source)
    (beta : BandSmoothBoundary L sigma gamma ell) (betaBand : OriginalBoundaryBand ceiling beta) :
    OriginalBoundaryBand ceiling (forcedBoundary admissible source beta) := by
  intro cell outside mode
  have absent := forceRadial_cell_zero admissible source.1 cell (sourceBand cell outside).1
  have angularZero := (congrArg (angularClosedJet mode) absent).trans (map_zero (angularClosedJetLinear 1 mode))
  have endpoint := congrArg (fun jet : ClosedJet 1 => jet.value (boundaryDiskPoint 0)) angularZero
  rw [forcedBoundary_coefficient, betaBand cell outside mode, endpoint]
  simp only [closedJet_value_zero, ContinuousMap.zero_apply, sub_self, smul_zero]

/-- Native AN17 estimate for the common coherent boundary, at every order. -/
theorem forcedData_native_bound (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    (source : SmoothCapSource L sigma gamma ell) (beta : BandSmoothBoundary L sigma gamma ell) :
    ‖apSmoothGrade L sigma gamma ell 1 grade (scalarForcing admissible source)‖ +
      ‖(forcedBoundary admissible source beta).grade grade‖ ≤
        (forcingConstant L gamma grade + boundaryForcingConstant L sigma gamma grade) *
          ‖capSourceGrade grade source‖ + ‖beta.grade grade‖ :=
  actualScalarForcing_consumer admissible grade source (beta.grade grade)

end Grad.ActualForcingSupport
