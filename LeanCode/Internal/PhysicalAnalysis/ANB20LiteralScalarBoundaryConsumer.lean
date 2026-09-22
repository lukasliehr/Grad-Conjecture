import ANB19ExactOriginalScalarConsumer

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.BoundedScalarInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.InhomogeneousHighRobin Grad.CircularNormalLift
open Grad.NonlinearDivision
open Grad.BoundaryTrace Grad.ActualSmoothRobin Grad.ActualAngularInverse Grad.OrdinaryDiskCalculus

theorem original_scalar_literal_robin {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (source : APSmooth length sigma gamma scale 1) (boundary : BandSmoothBoundary length sigma gamma scale)
    (field : APSmooth length sigma gamma scale 1) (laws : IsOriginalScalarSolution admissible source boundary field)
    (cell mode : ℤ) (grade : ℕ) :
    fourierCoeff (fun angle : CellCircle =>
      (robinResidualJet (excludedAngularJet lowAngularModes (apSmoothJet admissible 1 cell field))).value (boundaryDiskPoint angle)) mode =
      apBoundaryCoefficient length sigma gamma scale (grade + 1) (boundary.grade grade) (mode, cell) := by
  let high := excludedAngularJet lowAngularModes (apSmoothJet admissible 1 cell field)
  have trace := (laws cell).2.2.2 grade
  have identity := congrArg (fun data => apBoundaryCoefficient 1 0 0 1 (grade + 1) data (mode, 0)) trace
  have actual := (congrArg (fun data => apBoundaryCoefficient 1 0 0 1 (grade + 1) data (mode, 0))
    (ordinaryRobinTrace_core grade high)).trans
      ((ordinaryBoundaryTrace_core_coefficient (grade + 1) (by omega) (robinResidualJet high) (mode, 0)).trans (if_pos rfl))
  exact actual.symm.trans (identity.trans (smoothBoundaryCell_coefficient admissible boundary cell grade mode))

/-- Literal original B = I + 4 R^-2, not the high-only multiplier, together
with the exact physical high Robin Fourier coefficients of the original boundary. -/
theorem actual_original_scalar_boundary_consumer {length sigma gamma scale : ℝ}
    (admissible : Admissible length sigma gamma scale) (ceiling : ℝ) (parameters : PhaseParameters)
    (source : APSmooth length sigma gamma scale 1) (excluded : OriginalSourceNonexceptional admissible source)
    (sourceBand : OriginalSourceBand admissible ceiling source) (boundary : BandSmoothBoundary length sigma gamma scale)
    (high : OriginalBoundaryHigh boundary) (boundaryBand : OriginalBoundaryBand ceiling boundary) :
    let solution := apBandScalarInverse admissible ceiling parameters source excluded boundary high;
    ∀ cell : ℤ, let jet := apSmoothJet admissible 1 cell solution;
      -laplacianJet jet + ((((cell : ℝ) * scale / length) ^ 2 : ℝ) : ℂ) •
        (jet + (4 : ℂ) • shiftInverseJet 0 (shiftInverseJet 0 jet)) = apSmoothJet admissible 1 cell source ∧
      (∀ mode : ℤ, mode = 1 ∨ mode = -1 → Grad.ActualCenterVolterra.CenterPinned (angularClosedJet mode jet)) ∧
      ∀ (grade : ℕ) (mode : ℤ),
        fourierCoeff (fun angle : CellCircle =>
          (robinResidualJet (excludedAngularJet lowAngularModes jet)).value (boundaryDiskPoint angle)) mode =
            apBoundaryCoefficient length sigma gamma scale (grade + 1) (boundary.grade grade) (mode, cell) := by
  dsimp only
  intro cell
  have laws := apBandScalarInverse_specification admissible ceiling parameters source excluded sourceBand boundary high boundaryBand cell
  refine ⟨?_, laws.2.2.1, ?_⟩
  · have equation := laws.2.1
    rw [fullScalarJet_formula, fullBJet_formula] at equation
    exact equation
  · intro grade mode
    exact original_scalar_literal_robin admissible source boundary _
      (apBandScalarInverse_specification admissible ceiling parameters source excluded sourceBand boundary high boundaryBand) cell mode grade

end Grad.BoundedScalarInverse
