import ANB13BoundaryCellSlicing

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.BoundedScalarInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularNormalLift
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.CircularHighWeak Grad.OrdinaryDiskCalculus
local instance (priority := 2000) rowGainUnitSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) := unitNormedSpace grade
local instance (priority := 2000) rowGainBoundarySpace (grade : ℕ) : NormedSpace ℂ (normalBoundaryGrade grade) :=
  (normalBoundaryGrade grade).normedSpace

def bandScalarGainConstant (length gamma ceiling : ℝ) (grade : ℕ) (large : 3 ≤ grade) : ℝ :=
  originalBandRowConstant length gamma ceiling (grade + 2) * scalarGainConstant grade large ceiling *
    (bandMultiplicationConstant length gamma ceiling grade + bandWeightCeiling length gamma ceiling)

theorem bandScalarGainConstant_nonnegative (length gamma ceiling : ℝ) (nonnegative : 0 ≤ gamma)
    (grade : ℕ) (large : 3 ≤ grade) : 0 ≤ bandScalarGainConstant length gamma ceiling grade large :=
  mul_nonneg (mul_nonneg (originalBandRowConstant_nonnegative _ _ _ nonnegative _) (scalarGainConstant_nonnegative _ _ _))
    (add_nonneg (bandMultiplicationConstant_nonnegative _ _ _ nonnegative _) (Real.exp_pos _).le)

theorem smoothBoundaryCell_high {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (boundary : BandSmoothBoundary length sigma gamma scale)
    (high : ∀ mode ∈ lowAngularModes, ∀ cell,
      apBoundaryCoefficient length sigma gamma scale 1 (boundary.grade 0) (mode, cell) = 0) (cell : ℤ) :
    BoundaryIsHigh (smoothBoundaryCell admissible boundary cell) := by
  intro mode member
  exact (smoothBoundaryCell_coefficient admissible boundary cell 0 mode).trans (high mode member cell)

private theorem pair_bound (first second a b : ℝ) (aNonnegative : 0 ≤ a) (bNonnegative : 0 ≤ b)
    (firstNonnegative : 0 ≤ first) (secondNonnegative : 0 ≤ second) :
    a * first + b * second ≤ (a + b) * (first + second) := by
  nlinarith [mul_nonneg aNonnegative secondNonnegative, mul_nonneg bNonnegative firstNonnegative]

/-- Original weighted Cartesian row against original weighted boundary column.
No cell-count factor and no change of analytic width occur. -/
theorem scalarInverse_original_row_gain {length sigma gamma scale : ℝ}
    (admissible : Admissible length sigma gamma scale) (ceiling : ℝ) (cell : ℤ)
    (band : InCellBand length scale ceiling cell) (grade : ℕ) (large : 3 ≤ grade)
    (parameters : PhaseParameters) (source : ClosedJet 1) (excluded : IsScalarNonexceptional source)
    (boundary : BandSmoothBoundary length sigma gamma scale)
    (high : BoundaryIsHigh (smoothBoundaryCell admissible boundary cell)) :
    ‖apRowLinear (grade := grade + 2) length sigma gamma scale cell
      (scalarInverseJet parameters ((cell : ℝ) * scale / length) source (smoothBoundaryCell admissible boundary cell))‖ ≤
      bandScalarGainConstant length gamma ceiling grade large *
        (‖apRowLinear (grade := grade) length sigma gamma scale cell source‖ + ‖hilbertColumn (boundary.grade grade) cell‖) := by
  let scalar : ℂ := Real.exp (sigma * Grad.CellWeights.cellWeight cell)
  let data := smoothBoundaryCell admissible boundary cell
  have first := originalBandRow_le_flat admissible ceiling cell band (grade + 2)
    (scalarInverseJet parameters ((cell : ℝ) * scale / length) source data)
  have homogeneity := scalarInverseJet_smul scalar parameters ((cell : ℝ) * scale / length) source excluded data high
  have second := scalarInverseJet_native_gain grade large ceiling parameters ((cell : ℝ) * scale / length) band
    (scalar • source) (boundarySmul scalar data)
  have output : unitDiskCoreInto (grade + 2) (flatWeightedJet sigma cell
      (scalarInverseJet parameters ((cell : ℝ) * scale / length) source data)) =
      unitDiskCoreInto (grade + 2) (scalarInverseJet parameters ((cell : ℝ) * scale / length)
        (scalar • source) (boundarySmul scalar data)) := congrArg (unitDiskCoreInto (grade + 2)) homogeneity.symm
  have sourceBound := flat_le_originalBandRow admissible ceiling cell band grade source
  have boundaryBound : ‖(boundarySmul scalar data).grade grade‖ ≤
      bandWeightCeiling length gamma ceiling * ‖hilbertColumn (boundary.grade grade) cell‖ := by
    change ‖scalar • boundaryCellSlice admissible grade cell (boundary.grade grade)‖ ≤ _
    rw [boundaryCellSlice_flat]
    exact boundaryFlatSlice_norm admissible ceiling cell band grade _
  have inputBound := add_le_add sourceBound boundaryBound
  have combined := inputBound.trans (pair_bound _ _ _ _
    (bandMultiplicationConstant_nonnegative _ _ _ (admissible_gamma_nonnegative admissible) _)
    (Real.exp_pos _).le (norm_nonneg _) (norm_nonneg _))
  have native := second.trans (mul_le_mul_of_nonneg_left combined (scalarGainConstant_nonnegative _ _ _))
  have transported := (congrArg norm output).le.trans native
  exact first.trans ((mul_le_mul_of_nonneg_left transported
    (originalBandRowConstant_nonnegative _ _ _ (admissible_gamma_nonnegative admissible) _)).trans_eq (by
      unfold bandScalarGainConstant
      ring))

end Grad.BoundedScalarInverse
