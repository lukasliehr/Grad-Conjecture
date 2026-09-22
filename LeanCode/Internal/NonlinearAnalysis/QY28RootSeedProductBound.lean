import QY27InnerSeedBounds
import Q23SeedFieldDerivativeTower

noncomputable section

set_option maxRecDepth 4000
set_option maxHeartbeats 1200000

open scoped BigOperators

namespace Grad.MixedQuotientComposition

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.Constraints.Multipliers

theorem seedFieldCoreDerivative_compact_bound
    (parameters : PhaseParameters) (grade order : ℕ)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ seed ∈ seedPatch, ∀ directions : Fin order → Seed.Parameters,
        originalGradeNorm grade (q23SeedFieldCoreDerivative parameters order seed directions) ≤
          constant * ∏ position, ‖directions position‖ := by
  obtain ⟨constant, nonneg, bound⟩ := seedFieldDerivative_compact_bound
    parameters grade order seedPatch compact insidePatch
  refine ⟨constant, nonneg, fun seed member directions => ?_⟩
  have result := bound seed member directions
  rw [completedTameSeedFieldFamily_all_orders_core parameters grade order seed (insidePatch member),
    q23ACoreEta_norm] at result
  exact result

theorem seedFieldCoreDerivative_uniform_bound
    (parameters : PhaseParameters) (grade order : ℕ)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ count, count ≤ order → ∀ seed ∈ seedPatch,
      ∀ directions : Fin count → Input parameters,
        originalGradeNorm grade (q23SeedFieldCoreDerivative parameters count seed
          (fun position => (directions position).1)) ≤
          constant * ∏ position, directionNorm 4 (directions position) := by
  choose constants nonneg bounds using
    fun count => seedFieldCoreDerivative_compact_bound parameters grade count seedPatch compact insidePatch
  refine ⟨∑ count ∈ Finset.range (order + 1), constants count,
    Finset.sum_nonneg fun count _ => nonneg count, ?_⟩
  intro count countLe seed member directions
  apply (bounds count seed member (fun position => (directions position).1)).trans
  apply (mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun position _ => seedNorm_le_directionNorm 4 (directions position))) (nonneg count)).trans
  apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun _ _ => directionNorm_nonneg _ _)
  exact Finset.single_le_sum (fun c _ => nonneg c) (Finset.mem_range.mpr (by omega))

theorem assignmentFiber_one_eq_compl_zero {order : ℕ} (assignment : Fin order → Fin 2) :
    assignmentFiber assignment 1 = (assignmentFiber assignment 0)ᶜ := by
  ext position
  rw [mem_assignmentFiber, Finset.mem_compl, mem_assignmentFiber]
  omega

/-- One actual root/seed allocation term, in either seed derivative slot
convention. The seed factors occupy precisely the root block's complement. -/
theorem mixedRootSeedTerm_bound
    (parameters : PhaseParameters) (grade order : ℕ)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : Input parameters) (directions : Fin order → Input parameters),
        base.1 ∈ seedPatch → ChartAxisCondition base.2.2 →
        ∀ (assignment : Fin order → Fin 2)
          (seedOrder : Equiv.Perm (Fin (assignmentFiber assignment 1).card)),
        originalGradeNorm grade (tameScalarMultiplier 3
          (rootDerivativeFamily (assignmentFiber assignment 0).card base.2.2.1
            (fun position => (fiberTuple assignment 0 directions position).2.2.1))
          (q23SeedFieldCoreDerivative parameters (assignmentFiber assignment 1).card base.1
            (fun position => (fiberTuple assignment 1 directions (seedOrder position)).1))) ≤
          constant * inputOneHigh grade 4 base directions := by
  obtain ⟨rootC, rootNonneg, rootBound⟩ := mixedRootDerivative_fiber_bound (parameters := parameters) grade order
  obtain ⟨seedC, seedNonneg, seedBound⟩ := seedFieldCoreDerivative_uniform_bound
    parameters grade order seedPatch compact insidePatch
  have multiplierNonneg := tameMultiplierConstant_nonneg (parameters := parameters) grade
  refine ⟨multiplierConstant grade parameters.gamma * seedC * rootC, by positivity,
    fun base directions member axis assignment seedOrder => ?_⟩
  have cardLe : (assignmentFiber assignment 1).card ≤ order :=
    (Finset.card_le_univ _).trans (by rw [Fintype.card_fin])
  have seedEstimate := seedBound _ cardLe base.1 member
    (fun position => fiberTuple assignment 1 directions (seedOrder position))
  rw [Equiv.prod_comp seedOrder (fun position => directionNorm 4 (fiberTuple assignment 1 directions position))]
    at seedEstimate
  change originalGradeNorm grade _ ≤ seedC *
    ∏ position, directionNorm 4 (directions (fiberEnumeration assignment 1 position)) at seedEstimate
  rw [prod_fiber_eq assignment 1 (fun position => directionNorm 4 (directions position))] at seedEstimate
  conv at seedEstimate => rhs; rw [assignmentFiber_one_eq_compl_zero]
  have rootEstimate := rootBound base directions axis assignment 0
  have productEstimate := tameScalarMultiplier_bound 3
    (rootDerivativeFamily (assignmentFiber assignment 0).card base.2.2.1
      (fun position => (fiberTuple assignment 0 directions position).2.2.1))
    (q23SeedFieldCoreDerivative parameters (assignmentFiber assignment 1).card base.1
      (fun position => (fiberTuple assignment 1 directions (seedOrder position)).1)) grade
  apply productEstimate.trans
  calc
    _ ≤ multiplierConstant grade parameters.gamma *
        coefficientEnvelope grade
          (rootDerivativeFamily (assignmentFiber assignment 0).card base.2.2.1
            (fun position => (fiberTuple assignment 0 directions position).2.2.1)) *
        (seedC * ∏ position ∈ (assignmentFiber assignment 0)ᶜ, directionNorm 4 (directions position)) :=
      mul_le_mul_of_nonneg_left seedEstimate
        (mul_nonneg multiplierNonneg (coefficientEnvelope_nonneg _ _))
    _ = (multiplierConstant grade parameters.gamma * seedC) *
        (coefficientEnvelope grade
          (rootDerivativeFamily (assignmentFiber assignment 0).card base.2.2.1
            (fun position => (fiberTuple assignment 0 directions position).2.2.1)) *
          ∏ position ∈ (assignmentFiber assignment 0)ᶜ, directionNorm 4 (directions position)) := by ring
    _ ≤ (multiplierConstant grade parameters.gamma * seedC) *
        (rootC * inputOneHigh grade 4 base directions) :=
      mul_le_mul_of_nonneg_left rootEstimate (mul_nonneg multiplierNonneg seedNonneg)
    _ = _ := by ring

end Grad.MixedQuotientComposition
