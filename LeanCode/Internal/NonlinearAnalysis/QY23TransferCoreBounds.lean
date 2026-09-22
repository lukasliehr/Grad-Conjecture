import QY22MixedRootBound
import Q23SeedTransferReassemblyTower

noncomputable section

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.MixedQuotientComposition

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct

theorem q23ACoreEta_norm (parameters : PhaseParameters) (dimension grade : ℕ)
    (field : ACore parameters dimension) :
    ‖q23ACoreEta parameters dimension grade field‖ = originalGradeNorm grade field :=
  aGradeEta_norm parameters (GradeCore.ofCoreLinear field)

/-- All actual N18 seed derivatives have same-grade original core bounds,
uniform on the exact compact admissible seed patch. -/
theorem seedTransferCoreDerivative_compact_bound
    (parameters : PhaseParameters) (grade order : ℕ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (seed : Seed.Parameters), seed ∈ seedPatch →
      ∀ (directions : Fin order → Seed.Parameters) (field : ACore parameters 3),
        originalGradeNorm grade
          (q23SeedTransferCoreDerivative parameters reference insideR order seed directions field) ≤
          constant * (∏ position, ‖directions position‖) * originalGradeNorm grade field := by
  obtain ⟨constant, nonneg, bound⟩ :=
    completedSeedTransferParameterDerivative_compact_bound parameters grade order reference
      seedPatch compact insidePatch
  refine ⟨constant, nonneg, fun seed member directions field => ?_⟩
  have evaluation := (completedSeedTransferParameterDerivative parameters grade order reference seed directions).le_opNorm
    (q23ACoreEta parameters 3 grade field)
  rw [completedSeedTransferFamily_all_orders_core parameters grade reference insideR order seed
    (insidePatch member), q23ACoreEta_norm, q23ACoreEta_norm] at evaluation
  exact evaluation.trans
    (mul_le_mul_of_nonneg_right (bound seed member directions) (originalGradeNorm_nonnegative grade field))

/-- The preceding compact bound with the exact literal mixed direction
norms, for an arbitrary chosen field argument. -/
theorem seedTransferCoreDerivative_mixed_bound
    (parameters : PhaseParameters) (grade order low : ℕ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (seed : Seed.Parameters), seed ∈ seedPatch →
      ∀ (directions : Fin order → Input parameters) (field : ACore parameters 3),
        originalGradeNorm grade
          (q23SeedTransferCoreDerivative parameters reference insideR order seed
            (fun position => (directions position).1) field) ≤
          constant * (∏ position, directionNorm low (directions position)) * originalGradeNorm grade field := by
  obtain ⟨constant, nonneg, bound⟩ := seedTransferCoreDerivative_compact_bound
    parameters grade order reference insideR seedPatch compact insidePatch
  refine ⟨constant, nonneg, fun seed member directions field => ?_⟩
  apply (bound seed member (fun position => (directions position).1) field).trans
  apply mul_le_mul_of_nonneg_right _ (originalGradeNorm_nonnegative grade field)
  apply mul_le_mul_of_nonneg_left _ nonneg
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    (fun position _ => seedNorm_le_directionNorm low (directions position))

end Grad.MixedQuotientComposition
