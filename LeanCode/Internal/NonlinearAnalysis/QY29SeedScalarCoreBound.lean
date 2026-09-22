import QY27InnerSeedBounds
import Q23SeedScalarDerivativeTower

noncomputable section

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.MixedQuotientComposition

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds

theorem seedScalarCoreDerivative_compact_bound
    (parameters : PhaseParameters) (grade order : ℕ)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ seed ∈ seedPatch, ∀ directions : Fin order → Seed.Parameters,
        originalGradeNorm grade (q23SeedScalarCoreDerivative parameters order seed directions) ≤
          constant * ∏ position, ‖directions position‖ := by
  obtain ⟨constant, nonneg, bound⟩ := seedScalarDerivative_compact_bound
    parameters grade order seedPatch compact insidePatch
  refine ⟨constant, nonneg, fun seed member directions => ?_⟩
  have result := bound seed member directions
  rw [completedTameSeedScalarFamily_all_orders_core parameters grade order seed (insidePatch member),
    q23FieldEmbed_norm] at result
  exact result

/-- The actual seed-potential component of the mixed inner tower. Its
finite parameter derivative contributes only low direction factors. -/
theorem seedScalarCoreDerivative_mixed_bound
    (parameters : PhaseParameters) (grade order : ℕ)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : Input parameters), base.1 ∈ seedPatch →
      ∀ (directions : Fin order → Input parameters) (permutation : Equiv.Perm (Fin order)),
        originalGradeNorm grade (q23SeedScalarCoreDerivative parameters order base.1
          (fun position => (directions (permutation position)).1)) ≤
          constant * inputOneHigh grade 4 base directions := by
  obtain ⟨constant, nonneg, bound⟩ := seedScalarCoreDerivative_compact_bound
    parameters grade order seedPatch compact insidePatch
  refine ⟨constant, nonneg, fun base member directions permutation => ?_⟩
  have estimate := bound base.1 member (fun position => (directions (permutation position)).1)
  rw [Equiv.prod_comp permutation (fun position => ‖(directions position).1‖)] at estimate
  apply estimate.trans
  apply mul_le_mul_of_nonneg_left _ nonneg
  apply (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    (fun position _ => seedNorm_le_directionNorm 4 (directions position))).trans
  exact prod_directionNorm_le_inputOneHigh grade 4 base directions

end Grad.MixedQuotientComposition
