import ANG10RobinCommutation

noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
namespace Grad.CircularHighWeak
open Grad.CartesianState

def diskSelectedModes (modes : Finset ℤ) : DiskL2 1 →L[ℂ] DiskL2 1 :=
  ∑ mode ∈ modes, diskMode mode

theorem diskSelectedModes_apply (modes : Finset ℤ) (field : DiskL2 1) :
    diskSelectedModes modes field = ∑ mode ∈ modes, diskMode mode field := by
  simp only [diskSelectedModes, sum_apply]

theorem diskSelectedModes_coefficient (modes : Finset ℤ) (field : DiskL2 1) (other : ℤ) :
    diskMode other (diskSelectedModes modes field) = if other ∈ modes then diskMode other field else 0 := by
  rw [diskSelectedModes_apply, map_sum]
  simp_rw [diskMode_projection]
  simp

theorem diskSelectedModes_contract (modes : Finset ℤ) (field : DiskL2 1) :
    ‖diskSelectedModes modes field‖ ≤ ‖field‖ := by
  have bound : ‖diskFourier (diskSelectedModes modes field)‖ ≤ ‖diskFourier field‖ := by
    apply lp.norm_mono (by norm_num)
    intro other
    change ‖diskMode other (diskSelectedModes modes field)‖ ≤ ‖diskMode other field‖
    rw [diskSelectedModes_coefficient]
    split_ifs
    · exact le_refl _
    · exact (norm_zero.le).trans (norm_nonneg (diskMode other field))
  exact (diskFourier_norm (diskSelectedModes modes field)).symm.le.trans
    (bound.trans_eq (diskFourier_norm field))

def highSelectedModes (modes : Finset ℤ) : highDiskGrade →L[ℂ] highDiskGrade :=
  ∑ mode ∈ modes, highDiskMode mode

def highL2SelectedModes (modes : Finset ℤ) : highDiskL2 →L[ℂ] highDiskL2 :=
  ∑ mode ∈ modes, highL2Mode mode

theorem highL2SelectedModes_val (modes : Finset ℤ) (field : highDiskL2) :
    (highL2SelectedModes modes field).val = diskSelectedModes modes field.val := by
  simp only [highL2SelectedModes, diskSelectedModes, sum_apply, Submodule.coe_sum]
  rfl

theorem highL2SelectedModes_contract (modes : Finset ℤ) (field : highDiskL2) :
    ‖highL2SelectedModes modes field‖ ≤ ‖field‖ := by
  change ‖(highL2SelectedModes modes field).val‖ ≤ ‖field.val‖
  exact (congrArg norm (highL2SelectedModes_val modes field)).le.trans (diskSelectedModes_contract modes field.val)

theorem highRobinWeakInverse_selected (parameter : ℝ) (modes : Finset ℤ) (source : highDiskL2) :
    highSelectedModes modes (highRobinWeakInverse parameter source) =
      highRobinWeakInverse parameter (highL2SelectedModes modes source) := by
  simp only [highSelectedModes, highL2SelectedModes, sum_apply, map_sum]
  exact Finset.sum_congr rfl (fun mode _ => highRobinWeakInverse_angular parameter mode source)

/-- Immediate AN20 base consumer: every finite angular cutoff of the actual
weak solution has the same H1 bound, independent of cutoff and parameter. -/
theorem highRobinWeakInverse_selected_bound (parameter : ℝ) (modes : Finset ℤ) (source : highDiskL2) :
    ‖highSelectedModes modes (highRobinWeakInverse parameter source)‖ ≤ 2 * ‖source‖ := by
  exact (congrArg norm (highRobinWeakInverse_selected parameter modes source)).le.trans
    ((weakSolution_bound parameter (highL2SelectedModes modes source)).trans
      (mul_le_mul_of_nonneg_left (highL2SelectedModes_contract modes source) (by norm_num)))

end Grad.CircularHighWeak
