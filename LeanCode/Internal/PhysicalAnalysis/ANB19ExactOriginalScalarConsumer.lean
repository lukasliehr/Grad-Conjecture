import ANB18AllCellScalarLaws

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.BoundedScalarInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak Grad.CircularNormalLift
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Exact original nonexceptional scalar domain, equation, pinned center jets,
and actual high Robin trace in every cell. -/
def IsOriginalScalarSolution {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (source : APSmooth length sigma gamma scale 1) (boundary : BandSmoothBoundary length sigma gamma scale)
    (field : APSmooth length sigma gamma scale 1) : Prop :=
  ∀ cell : ℤ, IsNonexceptionalScalarSolution ((cell : ℝ) * scale / length) (apSmoothJet admissible 1 cell source)
    (smoothBoundaryCell admissible boundary cell) (apSmoothJet admissible 1 cell field)

theorem apBandScalarInverse_unique {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (ceiling : ℝ) (parameters : PhaseParameters) (source : APSmooth length sigma gamma scale 1)
    (excluded : OriginalSourceNonexceptional admissible source) (sourceBand : OriginalSourceBand admissible ceiling source)
    (boundary : BandSmoothBoundary length sigma gamma scale) (high : OriginalBoundaryHigh boundary)
    (boundaryBand : OriginalBoundaryBand ceiling boundary) (candidate : APSmooth length sigma gamma scale 1)
    (laws : IsOriginalScalarSolution admissible source boundary candidate) :
    candidate = apBandScalarInverse admissible ceiling parameters source excluded boundary high := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (scalarInverseJet_unique parameters _ _ _ (smoothBoundaryCell_high admissible boundary high cell) _ (laws cell)).trans
    (apBandScalarInverse_actual_cell admissible ceiling parameters source excluded sourceBand boundary high boundaryBand cell).symm

def allGradeBandConstant (length gamma ceiling : ℝ) (grade : ℕ) : ℝ :=
  if large : 3 ≤ grade then bandScalarGainConstant length gamma ceiling grade large else 0

theorem allGradeBandConstant_nonnegative (length gamma ceiling : ℝ) (nonnegative : 0 ≤ gamma) (grade : ℕ) :
    0 ≤ allGradeBandConstant length gamma ceiling grade := by
  unfold allGradeBandConstant
  split
  · exact bandScalarGainConstant_nonnegative _ _ _ nonnegative _ _
  · exact le_rfl

/-- AN36--38 bounded-frequency scalar assembly: constants come before sigma,
ell, source and boundary. The original AP/boundary norms and sigma are unchanged;
a single actual smooth AP inverse works simultaneously in every grade s >= 3. -/
theorem actual_bounded_frequency_scalar_inverse (length gamma ceiling : ℝ) (gammaNonnegative : 0 ≤ gamma) :
    ∃ constants : ℕ → ℝ, (∀ grade, 0 ≤ constants grade) ∧
      ∀ (sigma scale : ℝ) (admissible : Admissible length sigma gamma scale) (_parameters : PhaseParameters),
      ∀ source : APSmooth length sigma gamma scale 1, OriginalSourceNonexceptional admissible source →
        OriginalSourceBand admissible ceiling source → ∀ boundary : BandSmoothBoundary length sigma gamma scale,
        OriginalBoundaryHigh boundary → OriginalBoundaryBand ceiling boundary →
        ∃! solution : APSmooth length sigma gamma scale 1,
          IsOriginalScalarSolution admissible source boundary solution ∧ OriginalSourceBand admissible ceiling solution ∧
          ∀ grade : ℕ, 3 ≤ grade → ‖apSmoothGrade length sigma gamma scale 1 (grade + 2) solution‖ ≤
            constants grade * (‖apSmoothGrade length sigma gamma scale 1 grade source‖ + ‖boundary.grade grade‖) := by
  refine ⟨allGradeBandConstant length gamma ceiling, allGradeBandConstant_nonnegative _ _ _ gammaNonnegative, ?_⟩
  intro sigma scale admissible parameters source excluded sourceBand boundary high boundaryBand
  refine ⟨apBandScalarInverse admissible ceiling parameters source excluded boundary high, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact apBandScalarInverse_specification admissible ceiling parameters source excluded sourceBand boundary high boundaryBand
  · exact apBandScalarInverse_support admissible ceiling parameters source excluded boundary high
  · intro grade large
    rw [allGradeBandConstant, dif_pos large]
    exact apBandScalarInverse_native_gain admissible ceiling parameters source excluded boundary high grade large
  · intro candidate laws
    exact apBandScalarInverse_unique admissible ceiling parameters source excluded sourceBand boundary high boundaryBand candidate laws.1

end Grad.BoundedScalarInverse
