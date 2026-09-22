import AAT6SameInverseCommutation

noncomputable section
set_option maxHeartbeats 1000000

open Set Filter
open scoped Topology BigOperators

namespace Grad.AnnularGrades

open Grad.AnnularVariational Grad.ActualBandCompletion Grad.CartesianState
attribute [local instance] Classical.propDecidable

def fourierMask {Index : Type*} (keep : Set Index) (index : Index) : ℝ :=
  if index ∈ keep then 1 else 0

theorem fourierMask_bound {Index : Type*} (keep : Set Index) (index : Index) :
    |fourierMask keep index| ≤ 1 := by
  classical
  unfold fourierMask
  split_ifs <;> norm_num

theorem realLpDiagonal_mask {Index E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (keep : Set Index) (field : lp (fun _ : Index => E) 2) :
    realLpDiagonal (fourierMask keep) 1 (by norm_num) (fourierMask_bound keep) field = lpCut keep field := by
  classical
  apply lp.ext
  funext index
  rw [realLpDiagonal_apply, lpCut_apply]
  unfold fourierMask
  split_ifs <;> simp

theorem lpCut_finset_eq_sum {Index E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (support : Finset Index) (field : lp (fun _ : Index => E) 2) :
    lpCut (support : Set Index) field = ∑ index ∈ support, lp.single 2 index (field index) := by
  classical
  apply lp.ext
  funext index
  rw [lpCut_apply, lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.single_apply, Pi.single_apply, Finset.mem_coe]
  by_cases member : index ∈ support
  · rw [if_pos member, Finset.sum_eq_single_of_mem index member]
    · simp only [ite_true]
    · intro other _ different
      exact if_neg (Ne.symm different)
  · rw [if_neg member]
    symm
    apply Finset.sum_eq_zero
    intro other otherMember
    have different : index ≠ other := by
      intro equality
      subst other
      exact member otherMember
    exact if_neg different

theorem lpCut_finset_tendsto {Index E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (field : lp (fun _ : Index => E) 2) :
    Tendsto (fun support : Finset Index => lpCut (support : Set Index) field) atTop (𝓝 field) := by
  classical
  have convergence : Tendsto (fun support : Finset Index => ∑ index ∈ support, lp.single 2 index (field index))
      atTop (𝓝 field) := lp.hasSum_single (by norm_num) field
  simpa only [lpCut_finset_eq_sum] using convergence

def annularEnergyCut (lower length : ℝ) (positive : 0 < lower) (keep : Set HighAnnularMode) :
    annularEnergySpace lower length positive →L[ℂ] annularEnergySpace lower length positive :=
  annularEnergyDiagonal lower length positive (fourierMask keep) 1 (by norm_num) (fourierMask_bound keep)

theorem annularEnergyCut_val (lower length : ℝ) (positive : 0 < lower) (keep : Set HighAnnularMode)
    (field : annularEnergySpace lower length positive) :
    (annularEnergyCut lower length positive keep field).val = lpCut keep field.val :=
  realLpDiagonal_mask keep field.val

theorem annularEnergyCut_bound (lower length : ℝ) (positive : 0 < lower) (keep : Set HighAnnularMode)
    (field : annularEnergySpace lower length positive) :
    ‖annularEnergyCut lower length positive keep field‖ ≤ ‖field‖ := by
  simpa only [annularEnergyCut, one_mul] using
    annularEnergyDiagonal_bound lower length positive (fourierMask keep) 1 (by norm_num) (fourierMask_bound keep) field

/-- Full energy convergence of the literal finite Fourier cuts. -/
theorem annularEnergyCut_tendsto (lower length : ℝ) (positive : 0 < lower)
    (field : annularEnergySpace lower length positive) :
    Tendsto (fun support : Finset HighAnnularMode => annularEnergyCut lower length positive (support : Set HighAnnularMode) field)
      atTop (𝓝 field) := by
  apply tendsto_subtype_rng.mpr
  simpa only [annularEnergyCut_val] using lpCut_finset_tendsto field.val

end Grad.AnnularGrades
