import AKDN25LiteralFluxEulerRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.OriginalCartesianTameEstimate

/-- Literal derivative allocations of the phase and physical flux formula.
Triples record coefficient rank, input frequency grade, and input Euler rank. -/
def nativeEulerAllocations (rank grade : ℕ) : List (ℕ × ℕ × ℕ) :=
  (eulerLeibnizTerms rank).map (fun term => (0,grade+1,term.2)) ++
  (eulerLeibnizTerms rank).flatMap (fun flux =>
    (eulerLeibnizTerms flux.2).flatMap (fun row =>
      (eulerLeibnizTerms row.2).flatMap (fun input =>
        [(row.1,grade+1,input.2),(row.1+grade+1,0,input.2)])))

/-- Every term of the actual differentiated native equation has strictly
lower Euler rank and preserves the original total derivative allocation. -/
theorem nativeEulerAllocations_rank (rank grade : ℕ) (term : ℕ × ℕ × ℕ)
    (member : term ∈ nativeEulerAllocations rank grade) :
    term.2.2 ≤ rank ∧ term.1+term.2.1+term.2.2 ≤ rank+grade+1 := by
  rw [nativeEulerAllocations,List.mem_append] at member
  rcases member with phase | flux
  · obtain ⟨entry,inside,equal⟩ := List.mem_map.mp phase
    subst term
    have allocated := eulerLeibnizTerms_rank rank entry inside
    dsimp only
    omega
  · obtain ⟨outer,outerMember,inside⟩ := List.mem_flatMap.mp flux
    obtain ⟨row,rowMember,inside⟩ := List.mem_flatMap.mp inside
    obtain ⟨input,inputMember,inside⟩ := List.mem_flatMap.mp inside
    have outerRank := eulerLeibnizTerms_rank rank outer outerMember
    have rowRank := eulerLeibnizTerms_rank outer.2 row rowMember
    have inputRank := eulerLeibnizTerms_rank row.2 input inputMember
    simp only [List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with equal | equal <;> subst term <;> dsimp only <;> omega

theorem listFlatMap_real_sum {Index Item : Type*} (terms : List Index) (expand : Index → List Item) (value : Item → ℝ) :
    ((terms.flatMap expand).map value).sum = (terms.map (fun term => ((expand term).map value).sum)).sum := by
  induction terms with
  | nil => rfl
  | cons term terms previous =>
      simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons,previous]

theorem eulerAllocationSum_list (values : ℕ → ℕ → ℝ) (terms : List (ℕ × ℕ)) :
    (terms.map (fun term => values term.1 term.2)).sum = eulerAllocationSum values terms := by
  induction terms with
  | nil => rfl
  | cons term terms previous =>
      change values term.1 term.2+(terms.map (fun term => values term.1 term.2)).sum =
        values term.1 term.2+eulerAllocationSum values terms
      rw [previous]

/-- The finite collector is exactly the phase term plus the nested flux,
physical-row and kinematic-input Leibniz sums used by the checked estimates. -/
theorem nativeEulerAllocations_sum (rank grade : ℕ) (values : ℕ → ℕ → ℕ → ℝ) :
    ((nativeEulerAllocations rank grade).map (fun term => values term.1 term.2.1 term.2.2)).sum =
      eulerAllocationSum (fun _ terminal => values 0 (grade+1) terminal) (eulerLeibnizTerms rank)+
      eulerAllocationSum (fun _ rowRank =>
        eulerAllocationSum (fun coefficient inputRank =>
          eulerAllocationSum (fun _ terminal => values coefficient (grade+1) terminal+
            values (coefficient+grade+1) 0 terminal) (eulerLeibnizTerms inputRank))
          (eulerLeibnizTerms rowRank)) (eulerLeibnizTerms rank) := by
  unfold nativeEulerAllocations
  simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def,listFlatMap_real_sum,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  simp only [←eulerAllocationSum_list]

end Grad.OriginalCartesianTameEstimate
