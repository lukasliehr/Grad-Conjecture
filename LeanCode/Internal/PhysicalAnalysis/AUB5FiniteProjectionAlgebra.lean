import AUB2FiniteSmoothLinearity

noncomputable section
set_option maxHeartbeats 800000
namespace Grad.ActualUniformGlobal
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak

private theorem diskModes_ext {first second : DiskL2 1}
    (same : ∀ mode : ℤ, diskMode mode first = diskMode mode second) : first = second := by
  apply diskFourierIsometry.injective
  apply lp.ext
  funext mode
  exact same mode

theorem diskSelectedModes_comp_of_subset {small large : Finset ℤ} (subset : small ⊆ large)
    (field : DiskL2 1) : diskSelectedModes large (diskSelectedModes small field) = diskSelectedModes small field := by
  apply diskModes_ext
  intro mode
  rw [diskSelectedModes_coefficient, diskSelectedModes_coefficient]
  by_cases member : mode ∈ small
  · simp only [member, subset member, if_true]
  · by_cases larger : mode ∈ large <;> simp [member, larger]

theorem diskSelectedModes_highProjection (modes : Finset ℤ) (field : DiskL2 1) :
    diskSelectedModes modes (highL2Projection field) = highL2Projection (diskSelectedModes modes field) := by
  apply diskModes_ext
  intro mode
  rw [diskSelectedModes_coefficient, highL2Projection_coefficient, highL2Projection_coefficient,
    diskSelectedModes_coefficient]
  by_cases selected : mode ∈ modes <;> by_cases low : mode ∈ lowAngularModes <;> simp [selected, low]

theorem highL2Core_selected (modes : Finset ℤ) (core : ClosedJet 1) :
    highL2Core (selectedAngularJet modes core) = highL2SelectedModes modes (highL2Core core) := by
  apply Subtype.ext
  rw [highL2SelectedModes_val]
  change highL2Projection (closedL2Core (selectedAngularJet modes core)) =
    diskSelectedModes modes (highL2Projection (closedL2Core core))
  rw [← Grad.ActualFiniteGlobal.diskSelectedModes_core, diskSelectedModes_highProjection]

theorem highL2SelectedModes_comp_of_subset {small large : Finset ℤ} (subset : small ⊆ large)
    (field : highDiskL2) : highL2SelectedModes large (highL2SelectedModes small field) = highL2SelectedModes small field := by
  apply Subtype.ext
  rw [highL2SelectedModes_val, highL2SelectedModes_val]
  exact diskSelectedModes_comp_of_subset subset field.val

/-- Enlarging the solution cutoff does nothing to a source already supported
in a smaller finite set. This exact identity pays for Cauchy differences. -/
theorem finiteSmoothInverse_selected_of_subset (parameters : PhaseParameters) {small large : Finset ℤ}
    (subset : small ⊆ large) (parameter : ℝ) (core : ClosedJet 1) :
    finiteSmoothInverseLinear parameters large parameter (selectedAngularJet small core) =
      finiteSmoothInverseLinear parameters small parameter core := by
  apply closedL2Core_injective
  have first := finiteSmoothInverse_bulk parameters large parameter (selectedAngularJet small core)
  have second := finiteSmoothInverse_bulk parameters small parameter core
  exact first.trans ((congrArg (fun field : highDiskL2 => highDiskBulk (highRobinWeakInverse parameter field))
    ((congrArg (highL2SelectedModes large) (highL2Core_selected small core)).trans
      (highL2SelectedModes_comp_of_subset subset (highL2Core core)))).trans second.symm)

theorem finiteSmoothInverse_difference (parameters : PhaseParameters) (first second : Finset ℤ)
    (parameter : ℝ) (core : ClosedJet 1) :
    finiteSmoothInverseLinear parameters first parameter core - finiteSmoothInverseLinear parameters second parameter core =
      finiteSmoothInverseLinear parameters (first ∪ second) parameter
        (selectedAngularJet first core - selectedAngularJet second core) := by
  rw [map_sub, finiteSmoothInverse_selected_of_subset parameters Finset.subset_union_left,
    finiteSmoothInverse_selected_of_subset parameters Finset.subset_union_right]

end Grad.ActualUniformGlobal
