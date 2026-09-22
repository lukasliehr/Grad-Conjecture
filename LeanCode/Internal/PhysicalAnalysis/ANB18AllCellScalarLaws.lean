import ANB17OriginalAPScalarInverse

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.BoundedScalarInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak Grad.CircularNormalLift
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Compensated (APSmooth apSmoothJet apSmoothJet_ext)
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.InhomogeneousHighRobin
open Grad.ActualCenterVolterra Grad.NonlinearDivision Grad.NonlinearQuotientBounds

 theorem boundaryCell_outside_zero {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (ceiling : ℝ) (boundary : BandSmoothBoundary length sigma gamma scale) (supported : OriginalBoundaryBand ceiling boundary)
    (cell : ℤ) (outside : ¬ InCellBand length scale ceiling cell) (grade : ℕ) :
    (smoothBoundaryCell admissible boundary cell).grade grade = 0 := by
  apply normalBoundary_ext
  intro mode
  exact (smoothBoundaryCell_coefficient admissible boundary cell grade mode).trans
    ((boundary.coherent grade (mode, cell)).trans ((supported cell outside mode).trans (smul_zero _).symm))

theorem zero_centerPinned : CenterPinned (0 : ClosedJet 1) := by
  constructor
  · rfl
  · intro direction
    have zero := (Grad.GaugeCoefficients.Physical.Compensated.partialJetLinear 1 direction).map_zero
    change partialJet direction (0 : ClosedJet 1) = 0 at zero
    rw [zero]
    rfl

theorem zero_scalarSolution (frequency : ℝ) (boundary : NormalSmoothBoundary) (zero : ∀ grade, boundary.grade grade = 0) :
    IsNonexceptionalScalarSolution frequency 0 boundary 0 := by
  refine ⟨?_, (fullScalarLinear frequency).map_zero, ?_, ?_⟩
  · exact ⟨(angularClosedJetLinear 1 0).map_zero, (angularClosedJetLinear 1 2).map_zero,
      (angularClosedJetLinear 1 (-2)).map_zero⟩
  · intro mode _
    have projected := (angularClosedJetLinear 1 mode).map_zero
    change angularClosedJet mode (0 : ClosedJet 1) = 0 at projected
    rw [projected]
    exact zero_centerPinned
  · intro grade
    have projected := (excludedAngularJetLinear 1 lowAngularModes).map_zero
    change excludedAngularJet lowAngularModes (0 : ClosedJet 1) = 0 at projected
    rw [projected, map_zero, map_zero, zero grade]
    rfl

theorem bandScalarCell_specification {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (ceiling : ℝ) (parameters : PhaseParameters) (source : APSmooth length sigma gamma scale 1)
    (excluded : OriginalSourceNonexceptional admissible source) (sourceBand : OriginalSourceBand admissible ceiling source)
    (boundary : BandSmoothBoundary length sigma gamma scale) (high : OriginalBoundaryHigh boundary)
    (boundaryBand : OriginalBoundaryBand ceiling boundary) (cell : ℤ) :
    IsNonexceptionalScalarSolution ((cell : ℝ) * scale / length) (apSmoothJet admissible 1 cell source)
      (smoothBoundaryCell admissible boundary cell) (bandScalarCell admissible ceiling parameters source boundary cell) := by
  by_cases band : InCellBand length scale ceiling cell
  · rw [bandScalarCell_inside admissible ceiling parameters source boundary cell band]
    exact scalarInverseJet_specification parameters _ _ (excluded cell) _ (smoothBoundaryCell_high admissible boundary high cell)
  · rw [bandScalarCell_outside admissible ceiling parameters source boundary cell band, sourceBand cell band]
    exact zero_scalarSolution _ _ (boundaryCell_outside_zero admissible ceiling boundary boundaryBand cell band)

theorem apBandScalarInverse_specification {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (ceiling : ℝ) (parameters : PhaseParameters) (source : APSmooth length sigma gamma scale 1)
    (excluded : OriginalSourceNonexceptional admissible source) (sourceBand : OriginalSourceBand admissible ceiling source)
    (boundary : BandSmoothBoundary length sigma gamma scale) (high : OriginalBoundaryHigh boundary)
    (boundaryBand : OriginalBoundaryBand ceiling boundary) (cell : ℤ) :
    IsNonexceptionalScalarSolution ((cell : ℝ) * scale / length) (apSmoothJet admissible 1 cell source)
      (smoothBoundaryCell admissible boundary cell)
        (apSmoothJet admissible 1 cell (apBandScalarInverse admissible ceiling parameters source excluded boundary high)) := by
  rw [apBandScalarInverse_jet]
  exact bandScalarCell_specification admissible ceiling parameters source excluded sourceBand boundary high boundaryBand cell

/-- Every cell, including the zero cells outside the band, is the same actual
center-plus-high scalar inverse. -/
theorem apBandScalarInverse_actual_cell {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (ceiling : ℝ) (parameters : PhaseParameters) (source : APSmooth length sigma gamma scale 1)
    (excluded : OriginalSourceNonexceptional admissible source) (sourceBand : OriginalSourceBand admissible ceiling source)
    (boundary : BandSmoothBoundary length sigma gamma scale) (high : OriginalBoundaryHigh boundary)
    (boundaryBand : OriginalBoundaryBand ceiling boundary) (cell : ℤ) :
    apSmoothJet admissible 1 cell (apBandScalarInverse admissible ceiling parameters source excluded boundary high) =
      scalarInverseJet parameters ((cell : ℝ) * scale / length) (apSmoothJet admissible 1 cell source)
        (smoothBoundaryCell admissible boundary cell) :=
  scalarInverseJet_unique parameters _ _ _ (smoothBoundaryCell_high admissible boundary high cell) _
    (apBandScalarInverse_specification admissible ceiling parameters source excluded sourceBand boundary high boundaryBand cell)

end Grad.BoundedScalarInverse
