import ANB16BandCellFamily

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.BoundedScalarInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.ActualAngularInverse

def apBandScalarInverse {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (ceiling : ℝ) (parameters : PhaseParameters) (source : APSmooth length sigma gamma scale 1)
    (excluded : OriginalSourceNonexceptional admissible source) (boundary : BandSmoothBoundary length sigma gamma scale)
    (high : OriginalBoundaryHigh boundary) : APSmooth length sigma gamma scale 1 :=
  apLiteralSmooth length sigma gamma scale (bandScalarCell admissible ceiling parameters source boundary)
    (bandScalarCell_summable admissible ceiling parameters source excluded boundary high)

theorem apBandScalarInverse_jet {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (ceiling : ℝ) (parameters : PhaseParameters) (source : APSmooth length sigma gamma scale 1)
    (excluded : OriginalSourceNonexceptional admissible source) (boundary : BandSmoothBoundary length sigma gamma scale)
    (high : OriginalBoundaryHigh boundary) (cell : ℤ) :
    apSmoothJet admissible 1 cell (apBandScalarInverse admissible ceiling parameters source excluded boundary high) =
      bandScalarCell admissible ceiling parameters source boundary cell :=
  literalSmooth_jet admissible _ _ cell

theorem apBandScalarInverse_support {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (ceiling : ℝ) (parameters : PhaseParameters) (source : APSmooth length sigma gamma scale 1)
    (excluded : OriginalSourceNonexceptional admissible source) (boundary : BandSmoothBoundary length sigma gamma scale)
    (high : OriginalBoundaryHigh boundary) :
    OriginalSourceBand admissible ceiling (apBandScalarInverse admissible ceiling parameters source excluded boundary high) := by
  intro cell outside
  exact (apBandScalarInverse_jet admissible ceiling parameters source excluded boundary high cell).trans
    (bandScalarCell_outside admissible ceiling parameters source boundary cell outside)

/-- Genuine original AP H^s to H^(s+2), with the original circle H^(s+1/2)
source norm and unchanged sigma. The same AP smooth inverse is used in all grades. -/
theorem apBandScalarInverse_native_gain {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (ceiling : ℝ) (parameters : PhaseParameters) (source : APSmooth length sigma gamma scale 1)
    (excluded : OriginalSourceNonexceptional admissible source) (boundary : BandSmoothBoundary length sigma gamma scale)
    (high : OriginalBoundaryHigh boundary) (grade : ℕ) (large : 3 ≤ grade) :
    ‖apSmoothGrade length sigma gamma scale 1 (grade + 2)
      (apBandScalarInverse admissible ceiling parameters source excluded boundary high)‖ ≤
      bandScalarGainConstant length gamma ceiling grade large *
        (‖apSmoothGrade length sigma gamma scale 1 grade source‖ + ‖boundary.grade grade‖) := by
  have estimate := hilbertSynthesis_norm (bandScalarGainConstant length gamma ceiling grade large)
    (bandScalarGainConstant_nonnegative _ _ _ (admissible_gamma_nonnegative admissible) _ _)
    (apSmoothGrade length sigma gamma scale 1 grade source).val (hilbertColumnSizes (boundary.grade grade))
    (apSmoothGrade length sigma gamma scale 1 (grade + 2)
      (apBandScalarInverse admissible ceiling parameters source excluded boundary high)).val
    (fun cell => bandScalarCell_row_gain admissible ceiling parameters source excluded boundary high grade large cell)
  exact estimate.trans_eq (by rw [hilbertColumnSizes_norm]; rfl)

end Grad.BoundedScalarInverse
