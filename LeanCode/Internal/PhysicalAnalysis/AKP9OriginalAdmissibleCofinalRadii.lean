import AKP5ActualOriginalAnnularWeakLimit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.ActualAnnularExhaustion

/-- Fixed cofinal collars remain in the original c≤min(1/2,L) domain. -/
def originalExhaustionRadius (length : ℝ) (index : ℕ) : ℝ :=
  min (1 / 2 : ℝ) length / ((index : ℝ) + 1)

theorem originalExhaustionRadius_positive (length : ℝ) (lengthPositive : 0 < length) (index : ℕ) :
    0 < originalExhaustionRadius length index :=
  div_pos (lt_min (by norm_num) lengthPositive) (by positivity)

theorem originalExhaustionRadius_domain (length : ℝ) (lengthPositive : 0 < length) (index : ℕ) :
    originalExhaustionRadius length index ≤ min (1 / 2 : ℝ) length := by
  apply div_le_self (le_min (by norm_num) lengthPositive.le)
  have positive : 0 ≤ (index : ℝ) := Nat.cast_nonneg index
  linarith

theorem originalExhaustionRadius_half (length : ℝ) (lengthPositive : 0 < length) (index : ℕ) :
    originalExhaustionRadius length index ≤ 1 / 2 :=
  (originalExhaustionRadius_domain length lengthPositive index).trans (min_le_left _ _)

theorem originalExhaustionRadius_antitone (length : ℝ) (lengthPositive : 0 < length) :
    Antitone (originalExhaustionRadius length) := by
  intro first second order
  apply div_le_div_of_nonneg_left (le_min (by norm_num) lengthPositive.le) (by positivity)
  exact add_le_add (Nat.cast_le.mpr order) le_rfl

theorem originalExhaustionRadius_tendsto (length : ℝ) :
    Tendsto (originalExhaustionRadius length) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => min (1 / 2 : ℝ) length / ((n : ℝ) + 1)) atTop (𝓝 0)
  have constant : Tendsto (fun _ : ℕ => min (1 / 2 : ℝ) length) atTop (𝓝 (min (1 / 2 : ℝ) length)) := tendsto_const_nhds
  have limit := constant.mul tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [originalExhaustionRadius,mul_one_div,mul_zero] using limit

theorem originalExhaustionRadius_cofinal (length : ℝ) (lengthPositive : 0 < length) (collar : ℕ) :
    ∀ᶠ n in atTop, originalExhaustionRadius length n ≤ originalExhaustionRadius length collar :=
  ((originalExhaustionRadius_tendsto length).eventually
    (gt_mem_nhds (originalExhaustionRadius_positive length lengthPositive collar))).mono (fun _ smaller => smaller.le)

end Grad.ActualAnnularExhaustion
