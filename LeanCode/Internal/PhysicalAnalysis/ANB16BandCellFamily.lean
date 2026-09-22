import ANB15HilbertSynthesis

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.BoundedScalarInverse
attribute [local instance] Classical.propDecidable
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak Grad.CircularNormalLift
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.GaugeCoefficients.Algebra

abbrev OriginalBoundaryHigh {length sigma gamma scale : ℝ} (boundary : BandSmoothBoundary length sigma gamma scale) : Prop :=
  ∀ mode ∈ lowAngularModes, ∀ cell, apBoundaryCoefficient length sigma gamma scale 1 (boundary.grade 0) (mode, cell) = 0

abbrev OriginalSourceNonexceptional {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (source : APSmooth length sigma gamma scale 1) : Prop :=
  ∀ cell, IsScalarNonexceptional (apSmoothJet admissible 1 cell source)

abbrev OriginalSourceBand {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (ceiling : ℝ) (source : APSmooth length sigma gamma scale 1) : Prop :=
  ∀ cell, ¬ InCellBand length scale ceiling cell → apSmoothJet admissible 1 cell source = 0

abbrev OriginalBoundaryBand {length sigma gamma scale : ℝ} (ceiling : ℝ)
    (boundary : BandSmoothBoundary length sigma gamma scale) : Prop :=
  ∀ cell, ¬ InCellBand length scale ceiling cell → ∀ mode,
    apBoundaryCoefficient length sigma gamma scale 1 (boundary.grade 0) (mode, cell) = 0

/-- One actual smooth jet per cell, independent of Sobolev grade. -/
def bandScalarCell {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (ceiling : ℝ) (parameters : PhaseParameters) (source : APSmooth length sigma gamma scale 1)
    (boundary : BandSmoothBoundary length sigma gamma scale) (cell : ℤ) : ClosedJet 1 :=
  if InCellBand length scale ceiling cell then
    scalarInverseJet parameters ((cell : ℝ) * scale / length) (apSmoothJet admissible 1 cell source)
      (smoothBoundaryCell admissible boundary cell) else 0

theorem bandScalarCell_inside {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (ceiling : ℝ) (parameters : PhaseParameters) (source : APSmooth length sigma gamma scale 1)
    (boundary : BandSmoothBoundary length sigma gamma scale) (cell : ℤ) (band : InCellBand length scale ceiling cell) :
    bandScalarCell admissible ceiling parameters source boundary cell =
      scalarInverseJet parameters ((cell : ℝ) * scale / length) (apSmoothJet admissible 1 cell source)
        (smoothBoundaryCell admissible boundary cell) := if_pos band

theorem bandScalarCell_outside {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (ceiling : ℝ) (parameters : PhaseParameters) (source : APSmooth length sigma gamma scale 1)
    (boundary : BandSmoothBoundary length sigma gamma scale) (cell : ℤ) (outside : ¬ InCellBand length scale ceiling cell) :
    bandScalarCell admissible ceiling parameters source boundary cell = 0 := if_neg outside

theorem bandScalarCell_row_gain {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (ceiling : ℝ) (parameters : PhaseParameters) (source : APSmooth length sigma gamma scale 1)
    (excluded : OriginalSourceNonexceptional admissible source) (boundary : BandSmoothBoundary length sigma gamma scale)
    (high : OriginalBoundaryHigh boundary) (grade : ℕ) (large : 3 ≤ grade) (cell : ℤ) :
    ‖apRowLinear (grade := grade + 2) length sigma gamma scale cell (bandScalarCell admissible ceiling parameters source boundary cell)‖ ≤
      bandScalarGainConstant length gamma ceiling grade large *
        (‖(apSmoothGrade length sigma gamma scale 1 grade source).val cell‖ + ‖hilbertColumnSizes (boundary.grade grade) cell‖) := by
  by_cases band : InCellBand length scale ceiling cell
  · rw [bandScalarCell_inside admissible ceiling parameters source boundary cell band]
    have estimate := scalarInverse_original_row_gain admissible ceiling cell band grade large parameters
      (apSmoothJet admissible 1 cell source) (excluded cell) boundary (smoothBoundaryCell_high admissible boundary high cell)
    exact estimate.trans_eq (by rw [apSmoothJet_row]; simp [hilbertColumnSizes])
  · rw [bandScalarCell_outside admissible ceiling parameters source boundary cell band, map_zero, norm_zero]
    exact mul_nonneg (bandScalarGainConstant_nonnegative _ _ _ (admissible_gamma_nonnegative admissible) _ _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))

theorem bandScalarCell_summable {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (ceiling : ℝ) (parameters : PhaseParameters) (source : APSmooth length sigma gamma scale 1)
    (excluded : OriginalSourceNonexceptional admissible source) (boundary : BandSmoothBoundary length sigma gamma scale)
    (high : OriginalBoundaryHigh boundary) (grade : ℕ) :
    Memℓp (fun cell => apRowLinear (grade := grade) length sigma gamma scale cell
      (bandScalarCell admissible ceiling parameters source boundary cell)) 2 := by
  let upper := max 3 grade
  have large : 3 ≤ upper := le_max_left _ _
  apply hilbertSynthesis_mem (apLoweringConstant grade * bandScalarGainConstant length gamma ceiling upper large)
    (mul_nonneg (apLoweringConstant_nonnegative _) (bandScalarGainConstant_nonnegative _ _ _
      (admissible_gamma_nonnegative admissible) _ _))
    (apSmoothGrade length sigma gamma scale 1 upper source).val (hilbertColumnSizes (boundary.grade upper))
  intro cell
  exact (apLowerRow_bound length sigma gamma scale (show grade ≤ upper + 2 by dsimp [upper]; omega) cell _).trans
    ((mul_le_mul_of_nonneg_left (bandScalarCell_row_gain admissible ceiling parameters source excluded boundary high upper large cell)
      (apLoweringConstant_nonnegative _)).trans_eq (mul_assoc _ _ _).symm)

end Grad.BoundedScalarInverse
