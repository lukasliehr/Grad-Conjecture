import AKDN30ActualNativeNormRecurrence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.OriginalCartesianTameEstimate

/-- The finite terminal payment contains exactly the allowed pure native
and actual forcing terms. The filters preserve the original total rank. -/
def finiteEulerTerminal (total : ℕ) (budget : ℕ → ℝ) (unknown forcing : ℕ → ℕ → ℝ) : ℝ :=
  (∑ index : Fin (total+1) × Fin (total+1),
    if index.1.val+index.2.val ≤ total then budget index.1.val*unknown 0 index.2.val else 0)+
  ∑ index : Fin (total+1) × Fin (total+1) × Fin (total+1),
    if index.1.val+index.2.1.val+index.2.2.val+1 ≤ total then
      budget index.1.val*forcing index.2.1.val index.2.2.val else 0

theorem finiteEulerTerminal_nonnegative (total : ℕ) (budget : ℕ → ℝ) (unknown forcing : ℕ → ℕ → ℝ)
    (budget0 : ∀ rank, 0 ≤ budget rank) (unknown0 : ∀ order grade, 0 ≤ unknown order grade)
    (forcing0 : ∀ order grade, 0 ≤ forcing order grade) :
    0 ≤ finiteEulerTerminal total budget unknown forcing := by
  unfold finiteEulerTerminal
  apply add_nonneg <;> apply Finset.sum_nonneg <;> intro index _ <;> split_ifs
  · exact mul_nonneg (budget0 _) (unknown0 _ _)
  · exact le_rfl
  · exact mul_nonneg (budget0 _) (forcing0 _ _)
  · exact le_rfl

theorem finiteEulerTerminal_pure (total : ℕ) (budget : ℕ → ℝ) (unknown forcing : ℕ → ℕ → ℝ)
    (budget0 : ∀ rank, 0 ≤ budget rank) (unknown0 : ∀ order grade, 0 ≤ unknown order grade)
    (forcing0 : ∀ order grade, 0 ≤ forcing order grade)
    (extra grade : ℕ) (allocated : extra+grade ≤ total) :
    budget extra*unknown 0 grade ≤ finiteEulerTerminal total budget unknown forcing := by
  classical
  let pure := fun index : Fin (total+1) × Fin (total+1) =>
    if index.1.val+index.2.val ≤ total then budget index.1.val*unknown 0 index.2.val else 0
  let source := fun index : Fin (total+1) × Fin (total+1) × Fin (total+1) =>
    if index.1.val+index.2.1.val+index.2.2.val+1 ≤ total then budget index.1.val*forcing index.2.1.val index.2.2.val else 0
  have pure0 (index) : 0 ≤ pure index := by
    dsimp only [pure]; split_ifs
    · exact mul_nonneg (budget0 _) (unknown0 _ _)
    · exact le_rfl
  have source0 (index) : 0 ≤ source index := by
    dsimp only [source]; split_ifs
    · exact mul_nonneg (budget0 _) (forcing0 _ _)
    · exact le_rfl
  have selected := Finset.single_le_sum (fun index _ => pure0 index)
    (Finset.mem_univ ((⟨extra,by omega⟩ : Fin (total+1)),(⟨grade,by omega⟩ : Fin (total+1))))
  have bound : budget extra*unknown 0 grade ≤ ∑ index, pure index := by
    simpa only [pure,if_pos allocated] using selected
  exact bound.trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun index _ => source0 index)))

theorem finiteEulerTerminal_source (total : ℕ) (budget : ℕ → ℝ) (unknown forcing : ℕ → ℕ → ℝ)
    (budget0 : ∀ rank, 0 ≤ budget rank) (unknown0 : ∀ order grade, 0 ≤ unknown order grade)
    (forcing0 : ∀ order grade, 0 ≤ forcing order grade)
    (extra order grade : ℕ) (allocated : extra+order+grade+1 ≤ total) :
    budget extra*forcing order grade ≤ finiteEulerTerminal total budget unknown forcing := by
  classical
  let pure := fun index : Fin (total+1) × Fin (total+1) =>
    if index.1.val+index.2.val ≤ total then budget index.1.val*unknown 0 index.2.val else 0
  let source := fun index : Fin (total+1) × Fin (total+1) × Fin (total+1) =>
    if index.1.val+index.2.1.val+index.2.2.val+1 ≤ total then budget index.1.val*forcing index.2.1.val index.2.2.val else 0
  have pure0 (index) : 0 ≤ pure index := by
    dsimp only [pure]; split_ifs
    · exact mul_nonneg (budget0 _) (unknown0 _ _)
    · exact le_rfl
  have source0 (index) : 0 ≤ source index := by
    dsimp only [source]; split_ifs
    · exact mul_nonneg (budget0 _) (forcing0 _ _)
    · exact le_rfl
  have selected := Finset.single_le_sum (fun index _ => source0 index)
    (Finset.mem_univ ((⟨extra,by omega⟩ : Fin (total+1)),(⟨order,by omega⟩ : Fin (total+1)),(⟨grade,by omega⟩ : Fin (total+1))))
  have bound : budget extra*forcing order grade ≤ ∑ index, source index := by
    simpa only [source,if_pos allocated] using selected
  exact bound.trans (le_add_of_nonneg_left (Finset.sum_nonneg (fun index _ => pure0 index)))

theorem listMappedSum_mul_left {Index : Type*} (constant : ℝ) (terms : List Index) (values : Index → ℝ) :
    constant*(terms.map values).sum = (terms.map (fun index => constant*values index)).sum := by
  induction terms with
  | nil => exact mul_zero _
  | cons term terms previous =>
      simp only [List.map_cons,List.sum_cons,mul_add,previous]

theorem listConstantWeight_sum {Index : Type*} (constant : ℝ) (terms : List Index) :
    (terms.map (fun _ => constant)).sum = (terms.length : ℝ)*constant := by
  induction terms with
  | nil => simp only [List.map_nil,List.sum_nil,List.length_nil,Nat.cast_zero,zero_mul]
  | cons term terms previous =>
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one,previous]
      ring

end Grad.OriginalCartesianTameEstimate
