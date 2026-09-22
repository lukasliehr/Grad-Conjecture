import AUB6CompletedFiniteInverse

noncomputable section
set_option maxHeartbeats 1000000
namespace Grad.ActualUniformGlobal
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.OrdinaryDiskFaithfulness Grad.OrdinaryDiskCalculus Grad.AngularSobolevTruncation
attribute [local instance] unitNormedSpace

theorem highL2ProjectionInto_selected (modes : Finset ℤ) (field : DiskL2 1) :
    highL2ProjectionInto (diskSelectedModes modes field) =
      highL2SelectedModes modes (highL2ProjectionInto field) := by
  apply Subtype.ext
  rw [highL2SelectedModes_val]
  exact (diskSelectedModes_highProjection modes field).symm

theorem finiteCompletedInverse_selected_of_subset (grade : ℕ) (parameters : PhaseParameters)
    (parameter : ℝ) {small large : Finset ℤ} (subset : small ⊆ large) (source : unitDiskSobolev grade) :
    finiteCompletedInverse grade parameters parameter large (ordinarySelected grade small source) =
      finiteCompletedInverse grade parameters parameter small source := by
  apply ordinaryBulk_injective parameters (grade + 2)
  calc
    _ = highDiskBulk (highRobinWeakInverse parameter
        (highL2SelectedModes large (highL2ProjectionInto (unitDiskBulk grade (ordinarySelected grade small source))))) :=
      finiteCompletedInverse_bulk grade parameters parameter large _
    _ = highDiskBulk (highRobinWeakInverse parameter
        (highL2SelectedModes small (highL2ProjectionInto (unitDiskBulk grade source)))) := by
      apply congrArg (fun field : highDiskL2 => highDiskBulk (highRobinWeakInverse parameter field))
      exact (congrArg (fun bulk => highL2SelectedModes large (highL2ProjectionInto bulk))
        (ordinarySelected_bulk grade small source)).trans
        ((congrArg (highL2SelectedModes large) (highL2ProjectionInto_selected small (unitDiskBulk grade source))).trans
          (highL2SelectedModes_comp_of_subset subset (highL2ProjectionInto (unitDiskBulk grade source))))
    _ = _ := (finiteCompletedInverse_bulk grade parameters parameter small source).symm

/-- Exact difference identity for arbitrary completed sources. The union
cutoff acts on the genuine Sobolev difference of the source truncations. -/
theorem finiteCompletedInverse_difference (grade : ℕ) (parameters : PhaseParameters)
    (parameter : ℝ) (first second : Finset ℤ) (source : unitDiskSobolev grade) :
    finiteCompletedInverse grade parameters parameter first source - finiteCompletedInverse grade parameters parameter second source =
      finiteCompletedInverse grade parameters parameter (first ∪ second)
        (ordinarySelected grade first source - ordinarySelected grade second source) := by
  exact (congrArg₂ (fun first second : unitDiskSobolev (grade + 2) => first - second)
    (finiteCompletedInverse_selected_of_subset grade parameters parameter Finset.subset_union_left source)
    (finiteCompletedInverse_selected_of_subset grade parameters parameter Finset.subset_union_right source)).symm.trans
    ((finiteCompletedInverse grade parameters parameter (first ∪ second)).map_sub
      (ordinarySelected grade first source) (ordinarySelected grade second source)).symm

theorem finiteCompletedInverse_difference_bound (grade : ℕ) (ceiling : ℝ) (parameters : PhaseParameters)
    (parameter : ℝ) (bounded : |parameter| ≤ ceiling) (first second : Finset ℤ) (source : unitDiskSobolev grade) :
    ‖finiteCompletedInverse grade parameters parameter first source - finiteCompletedInverse grade parameters parameter second source‖ ≤
      finiteInverseConstant grade ceiling * ‖ordinarySelected grade first source - ordinarySelected grade second source‖ := by
  exact (congrArg (fun field : unitDiskSobolev (grade + 2) => ‖field‖)
    (finiteCompletedInverse_difference grade parameters parameter first second source)).le.trans
      (finiteCompletedInverse_uniform grade ceiling parameters parameter bounded _ _)

end Grad.ActualUniformGlobal
