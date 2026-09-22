import QY25MixedCurvatureBound
import Q23SeedScalarFamilies

noncomputable section

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

open scoped BigOperators ContDiff

namespace Grad.MixedQuotientComposition

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds

/-- Compact bounds for the actual seed field derivatives, at the original
output grade. Every finite seed coordinate factor remains explicit. -/
theorem seedFieldDerivative_compact_bound
    (parameters : PhaseParameters) (grade order : ℕ)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ seed ∈ seedPatch, ∀ directions : Fin order → Seed.Parameters,
        ‖iteratedFDeriv ℝ order (completedTameSeedFieldFamily parameters grade) seed directions‖ ≤
          constant * ∏ position, ‖directions position‖ := by
  obtain ⟨constant, bound⟩ := compact.exists_bound_of_continuousOn
    ((ContinuousOn.continuousOn_iteratedFDeriv (k := order)
      (completedTameSeedFieldFamily_contDiffOn parameters grade)
      Seed.parameterDomain_isOpen
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).mono insidePatch)
  refine ⟨max 0 constant, le_max_left _ _, fun seed member directions => ?_⟩
  have operatorBound := (bound seed member).trans (le_max_right 0 constant)
  exact ((iteratedFDeriv ℝ order (completedTameSeedFieldFamily parameters grade) seed).le_opNorm directions).trans
    (mul_le_mul_of_nonneg_right operatorBound (Finset.prod_nonneg fun _ _ => norm_nonneg _))

/-- Compact bounds for the actual normalized seed-potential derivatives.
Any grades internal to its fixed seed formula affect only the constant. -/
theorem seedScalarDerivative_compact_bound
    (parameters : PhaseParameters) (grade order : ℕ)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ seed ∈ seedPatch, ∀ directions : Fin order → Seed.Parameters,
        ‖iteratedFDeriv ℝ order (completedTameSeedScalarFamily parameters grade) seed directions‖ ≤
          constant * ∏ position, ‖directions position‖ := by
  obtain ⟨constant, bound⟩ := compact.exists_bound_of_continuousOn
    ((ContinuousOn.continuousOn_iteratedFDeriv (k := order)
      (completedTameSeedScalarFamily_contDiffOn parameters grade)
      Seed.parameterDomain_isOpen
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).mono insidePatch)
  refine ⟨max 0 constant, le_max_left _ _, fun seed member directions => ?_⟩
  have operatorBound := (bound seed member).trans (le_max_right 0 constant)
  exact ((iteratedFDeriv ℝ order (completedTameSeedScalarFamily parameters grade) seed).le_opNorm directions).trans
    (mul_le_mul_of_nonneg_right operatorBound (Finset.prod_nonneg fun _ _ => norm_nonneg _))

theorem seedTransferCoreDerivative_uniform_bound
    (parameters : PhaseParameters) (grade order : ℕ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ count, count ≤ order → ∀ seed ∈ seedPatch,
      ∀ (directions : Fin count → Input parameters) (field : ACore parameters 3),
        originalGradeNorm grade
          (q23SeedTransferCoreDerivative parameters reference insideR count seed
            (fun position => (directions position).1) field) ≤
          constant * (∏ position, directionNorm 4 (directions position)) * originalGradeNorm grade field := by
  have each count := seedTransferCoreDerivative_mixed_bound parameters grade count 4
    reference insideR seedPatch compact insidePatch
  choose constants nonneg bounds using each
  refine ⟨∑ count ∈ Finset.range (order + 1), constants count,
    Finset.sum_nonneg fun count _ => nonneg count, ?_⟩
  intro count countLe seed member directions field
  apply (bounds count seed member directions field).trans
  apply mul_le_mul_of_nonneg_right _ (originalGradeNorm_nonnegative grade field)
  apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun _ _ => directionNorm_nonneg _ _)
  exact Finset.single_le_sum (fun c _ => nonneg c) (Finset.mem_range.mpr (by omega))

end Grad.MixedQuotientComposition
