import AW3Phase

noncomputable section

open Grad.PDEBootstrap Grad.GenericCarriers
open scoped BigOperators

namespace Grad.AnalyticWeights.Higher

universe valueUniverse

theorem allocationFiber_card_sum (rank : ℕ) (allocation : Fin rank → Fin 3) :
    (allocationFiber allocation 0).card + (allocationFiber allocation 1).card +
      (allocationFiber allocation 2).card = rank := by
  have disjoint : Disjoint (allocationFiber allocation 1) (allocationFiber allocation 2) := by
    refine Finset.disjoint_left.mpr ?_
    intro position first second
    simp only [allocationFiber, Finset.mem_filter, Finset.mem_univ, true_and] at first second
    omega
  have complement : (allocationFiber allocation 0)ᶜ =
      allocationFiber allocation 1 ∪ allocationFiber allocation 2 := by
    ext position
    simp only [allocationFiber, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    generalize equality : allocation position = label
    fin_cases label <;> simp_all
  rw [add_assoc, ← Finset.card_union_of_disjoint disjoint, ← complement, Finset.card_add_card_compl]
  exact Fintype.card_fin rank

theorem allocation_order_arithmetic (phaseRank coefficientRank inputRank displacementOrder : ℕ)
    (membership : displacementOrder ∈ Finset.Icc 1 phaseRank) :
    1 ≤ coefficientRank + displacementOrder ∧
      (coefficientRank + displacementOrder) + (inputRank + (phaseRank - displacementOrder)) =
        phaseRank + coefficientRank + inputRank := by
  simp only [Finset.mem_Icc] at membership
  omega

theorem output_cell_allocation_bound (Value : Type valueUniverse)
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (rank : ℕ) (output input : ℤ) (value : Value) :
    ‖(Grad.CellWeights.cellWeight output ^ rank) • value‖ ≤
      ∑ displacementOrder ∈ Finset.range (rank + 1),
        (Nat.choose rank displacementOrder : ℝ) * |((output - input : ℤ) : ℝ)| ^ displacementOrder *
          ‖(Grad.CellWeights.cellWeight input ^ (rank - displacementOrder)) • value‖ := by
  have cellBound := (cellGoal output input).2
  have nonnegativeInput := (Grad.CellWeights.cellWeight_pos input).le
  rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (Grad.CellWeights.cellWeight_pos output).le _)]
  calc
    _ ≤ (Grad.CellWeights.cellWeight input + |((output - input : ℤ) : ℝ)|) ^ rank * ‖value‖ :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Grad.CellWeights.cellWeight_pos output).le cellBound rank) (norm_nonneg _)
    _ = ∑ displacementOrder ∈ Finset.range (rank + 1),
        (Nat.choose rank displacementOrder : ℝ) * |((output - input : ℤ) : ℝ)| ^ displacementOrder *
          ‖(Grad.CellWeights.cellWeight input ^ (rank - displacementOrder)) • value‖ := by
      rw [add_comm, add_pow, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro displacementOrder membership
      rw [norm_smul, Real.norm_of_nonneg (pow_nonneg nonnegativeInput _)]
      ring

theorem allocationGoal : AllocationGoal.{valueUniverse} :=
  ⟨allocationFiber_card_sum, allocation_order_arithmetic, output_cell_allocation_bound⟩

end Grad.AnalyticWeights.Higher
