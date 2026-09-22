import AAT7ActualFourierCutoffs
import AAT8ExactTangentialWeights

noncomputable section
set_option maxHeartbeats 1000000

open Set Filter
open scoped Topology BigOperators

namespace Grad.AnnularGrades

open Grad.AnnularVariational Grad.ActualBandCompletion
attribute [local instance] Classical.propDecidable

def finiteWeightMask (weight : HighAnnularMode → ℝ) (support : Finset HighAnnularMode) (mode : HighAnnularMode) : ℝ :=
  if mode ∈ support then weight mode else 0

def finiteWeightBound (weight : HighAnnularMode → ℝ) (support : Finset HighAnnularMode) : ℝ :=
  ∑ mode ∈ support, |weight mode|

theorem finiteWeightBound_nonnegative (weight : HighAnnularMode → ℝ) (support : Finset HighAnnularMode) :
    0 ≤ finiteWeightBound weight support :=
  Finset.sum_nonneg (fun mode _ => abs_nonneg (weight mode))

theorem finiteWeightMask_bound (weight : HighAnnularMode → ℝ) (support : Finset HighAnnularMode) (mode : HighAnnularMode) :
    |finiteWeightMask weight support mode| ≤ finiteWeightBound weight support := by
  classical
  unfold finiteWeightMask
  by_cases member : mode ∈ support
  · rw [if_pos member]
    exact Finset.single_le_sum (fun other _ => abs_nonneg (weight other)) member
  · rw [if_neg member, abs_zero]
    exact finiteWeightBound_nonnegative weight support

/-- Any square-summable scalar reweighting of an actual energy graph is
again in W. Finite weighted cuts preserve W, and converge in its literal
ambient energy norm. No weighted-graph membership is assumed. -/
theorem annularWeightedCoordinates_mem (lower length : ℝ) (positive : 0 < lower)
    (weight : HighAnnularMode → ℝ) (field : annularEnergySpace lower length positive)
    (weighted : AnnularEnergyAmbient lower)
    (coordinates : ∀ mode, weighted mode = (weight mode : ℂ) • field.val mode) :
    weighted ∈ annularEnergySpace lower length positive := by
  apply (LinearMap.range (finiteAnnularEnergyCore lower length positive)).isClosed_topologicalClosure.mem_of_tendsto
    (lpCut_finset_tendsto weighted)
  apply Filter.Eventually.of_forall
  intro support
  have equality : lpCut (support : Set HighAnnularMode) weighted =
      (annularEnergyDiagonal lower length positive (finiteWeightMask weight support) (finiteWeightBound weight support)
        (finiteWeightBound_nonnegative weight support) (finiteWeightMask_bound weight support) field).val := by
    apply lp.ext
    funext mode
    rw [lpCut_apply, annularEnergyDiagonal_apply, coordinates]
    unfold finiteWeightMask
    by_cases member : mode ∈ support <;> simp [member]
  rw [equality]
  exact (annularEnergyDiagonal lower length positive (finiteWeightMask weight support) (finiteWeightBound weight support)
    (finiteWeightBound_nonnegative weight support) (finiteWeightMask_bound weight support) field).property

/-- Literal grade membership in the original energy coordinates. -/
def HasAnnularEnergyGrade (lower length : ℝ) (positive : 0 < lower) (angular cell inserted : ℕ)
    (field : annularEnergySpace lower length positive) : Prop :=
  Memℓp (fun mode : HighAnnularMode => (annularGradeWeight angular cell inserted mode : ℂ) • field.val mode) 2

/-- Recover the actual weighted graph from its literal square summability. -/
def annularWeightedEnergy (lower length : ℝ) (positive : 0 < lower) (angular cell inserted : ℕ)
    (field : annularEnergySpace lower length positive)
    (grade : HasAnnularEnergyGrade lower length positive angular cell inserted field) :
    annularEnergySpace lower length positive :=
  ⟨⟨fun mode => (annularGradeWeight angular cell inserted mode : ℂ) • field.val mode, grade⟩,
    annularWeightedCoordinates_mem lower length positive (annularGradeWeight angular cell inserted) field _ (fun _ => rfl)⟩

def annularEnergyDecode (lower length : ℝ) (positive : 0 < lower) (angular cell inserted : ℕ) :
    annularEnergySpace lower length positive →L[ℂ] annularEnergySpace lower length positive :=
  annularEnergyDiagonal lower length positive (fun mode => (annularGradeWeight angular cell inserted mode)⁻¹)
    1 (by norm_num) (annularGradeWeight_inv_bound angular cell inserted)

theorem annularEnergyDecode_apply (lower length : ℝ) (positive : 0 < lower) (angular cell inserted : ℕ)
    (field : annularEnergySpace lower length positive) (mode : HighAnnularMode) :
    (annularEnergyDecode lower length positive angular cell inserted field).val mode =
      (((annularGradeWeight angular cell inserted mode)⁻¹ : ℝ) : ℂ) • field.val mode := rfl

theorem annularEnergyDecode_normalization (lower length : ℝ) (positive : 0 < lower) (angular cell inserted : ℕ)
    (field : annularEnergySpace lower length positive) (mode : HighAnnularMode) :
    (annularGradeWeight angular cell inserted mode : ℂ) •
      (annularEnergyDecode lower length positive angular cell inserted field).val mode = field.val mode := by
  rw [annularEnergyDecode_apply, smul_smul, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (annularGradeWeight_pos angular cell inserted mode).ne', Complex.ofReal_one, one_smul]

theorem annularEnergyDecode_hasGrade (lower length : ℝ) (positive : 0 < lower) (angular cell inserted : ℕ)
    (field : annularEnergySpace lower length positive) :
    HasAnnularEnergyGrade lower length positive angular cell inserted
      (annularEnergyDecode lower length positive angular cell inserted field) := by
  have summable : Memℓp (fun mode : HighAnnularMode => field.val mode) 2 := field.val.property
  unfold HasAnnularEnergyGrade
  simp only [annularEnergyDecode_normalization]
  exact summable

theorem annularEnergyDecode_weighted (lower length : ℝ) (positive : 0 < lower) (angular cell inserted : ℕ)
    (field : annularEnergySpace lower length positive)
    (grade : HasAnnularEnergyGrade lower length positive angular cell inserted field) :
    annularEnergyDecode lower length positive angular cell inserted
      (annularWeightedEnergy lower length positive angular cell inserted field grade) = field := by
  apply Subtype.ext
  apply lp.ext
  funext mode
  rw [annularEnergyDecode_apply]
  change (((annularGradeWeight angular cell inserted mode)⁻¹ : ℝ) : ℂ) •
    ((annularGradeWeight angular cell inserted mode : ℂ) • field.val mode) = field.val mode
  rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (annularGradeWeight_pos angular cell inserted mode).ne',
    Complex.ofReal_one, one_smul]

/-- The decoder range is exactly the original literal weighted carrier. -/
theorem annularEnergyDecode_range_iff (lower length : ℝ) (positive : 0 < lower) (angular cell inserted : ℕ)
    (field : annularEnergySpace lower length positive) :
    field ∈ LinearMap.range (annularEnergyDecode lower length positive angular cell inserted).toLinearMap ↔
      HasAnnularEnergyGrade lower length positive angular cell inserted field := by
  constructor
  · rintro ⟨normalized, rfl⟩
    exact annularEnergyDecode_hasGrade lower length positive angular cell inserted normalized
  · intro grade
    exact ⟨annularWeightedEnergy lower length positive angular cell inserted field grade,
      annularEnergyDecode_weighted lower length positive angular cell inserted field grade⟩

end Grad.AnnularGrades
