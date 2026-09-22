import AOG1SelectedSourceAndOuter

noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators

namespace Grad.ActualFiniteGlobal
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.ActualInverseInduction Grad.InteriorLocalization
open Grad.ActualOuterCollar Grad.ClosedDiskRegularity Grad.OrdinaryDiskCalculus
open Grad.OrdinaryDiskReconstruction Grad.InteriorPeriodization
attribute [local instance] unitNormedSpace

/-- The original interior H2 gain and the constructed actual outer field
give global H2 for the SAME finite-selected weak inverse. -/
theorem finiteGlobalH2 (parameters : PhaseParameters) (modes : Finset ℤ) (parameter : ℝ)
    (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core) :
    ∃ state : unitDiskSobolev 2,
      unitDiskBulk 2 state = highDiskBulk (highRobinWeakInverse parameter (highL2SelectedModes modes source)) := by
  have interiorExists : ∃ interior : unitDiskSobolev 2,
      unitDiskBulk 2 interior = localizedDiskField parameter (highL2SelectedModes modes source) ∧
      ‖interior‖ ≤ interiorOrdinaryConstant * (1 + parameter ^ 2) * ‖highL2SelectedModes modes source‖ :=
    actualInteriorOrdinaryH2 parameters parameter (highL2SelectedModes modes source)
  obtain ⟨interior, interiorSame, _bound⟩ := interiorExists
  let outer := finiteOuterOrdinary 2 modes parameter source core same
  have outerSame := finiteOuterOrdinary_bulk 2 modes parameter source core same
  have interiorLiteral : unitDiskBulk 2 interior =
      diskScalar interiorCutoff.toFun interiorCutoff.smooth
        (highDiskBulk (highRobinWeakInverse parameter (highL2SelectedModes modes source))) := interiorSame
  refine ⟨interior + outer, ?_⟩
  exact ((unitDiskBulk 2).map_add interior outer).trans
    ((congrArg₂ (fun first second : DiskL2 1 => first + second) interiorLiteral outerSame).trans
      (actualCutoff_partition _))

/-- The all-grade step now supplies AIG's previously missing outer input
and the actual selected smooth forcing; only the preceding grade remains
as the inductive hypothesis. -/
theorem finiteGlobal_step (parameters : PhaseParameters) (grade : ℕ) (modes : Finset ℤ)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core)
    (state : unitDiskSobolev (grade + 1))
    (stateSame : unitDiskBulk (grade + 1) state =
      highDiskBulk (highRobinWeakInverse parameter (highL2SelectedModes modes source))) :
    ∃ global : unitDiskSobolev (grade + 2),
      unitDiskBulk (grade + 2) global =
        highDiskBulk (highRobinWeakInverse parameter (highL2SelectedModes modes source)) := by
  have construction := actualGlobal_inductionStep parameters grade parameter (highL2SelectedModes modes source)
    state (selectedForcing grade modes core) stateSame (selectedForcing_bulk grade modes source core same)
    (finiteOuterOrdinary (grade + 2) modes parameter source core same)
    (finiteOuterOrdinary_bulk (grade + 2) modes parameter source core same)
  obtain ⟨global, literal, _equation, _bound⟩ := construction
  exact ⟨global, literal⟩

/-- Actual global ordinary Sobolev representatives at every grade for the
same finite angular solution, obtained by induction from the proved H2 base. -/
theorem finiteGlobal_everyGrade (parameters : PhaseParameters) (modes : Finset ℤ)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core) :
    ∀ grade : ℕ, ∃ state : unitDiskSobolev grade,
      unitDiskBulk grade state = highDiskBulk (highRobinWeakInverse parameter (highL2SelectedModes modes source)) := by
  have base := finiteGlobalH2 parameters modes parameter source core same
  apply Nat.twoStepInduction
  · obtain ⟨state, literal⟩ := base
    exact ⟨unitLower (by omega : 0 ≤ 2) state, (unitLower_bulk (by omega : 0 ≤ 2) state).trans literal⟩
  · obtain ⟨state, literal⟩ := base
    exact ⟨unitLower (by omega : 1 ≤ 2) state, (unitLower_bulk (by omega : 1 ≤ 2) state).trans literal⟩
  · intro grade _ previous
    obtain ⟨state, literal⟩ := previous
    exact finiteGlobal_step parameters grade modes parameter source core same state literal

end Grad.ActualFiniteGlobal
