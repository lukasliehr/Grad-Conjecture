import QY28RootSeedProductBound
import QY26MixedAffineBounds

noncomputable section

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.MixedQuotientComposition

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds

theorem assignmentFiber_zero_eq_compl_one {order : ℕ} (assignment : Fin order → Fin 2) :
    assignmentFiber assignment 0 = (assignmentFiber assignment 1)ᶜ := by
  rw [assignmentFiber_one_eq_compl_zero, compl_compl]

/-- The actual N18 transfer/field allocation term. Its vector argument is
the literal zero/one affine field tower, and all seed derivatives are the
proved core-preserving derivatives of the actual completed transfer. -/
theorem mixedTransferTerm_bound
    (parameters : PhaseParameters) (grade order : ℕ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : Input parameters) (directions : Fin order → Input parameters),
        base.1 ∈ seedPatch →
        ∀ (assignment : Fin order → Fin 2)
          (seedOrder : Equiv.Perm (Fin (assignmentFiber assignment 0).card)),
        originalGradeNorm grade
          (q23SeedTransferCoreDerivative parameters reference insideR
            (assignmentFiber assignment 0).card base.1
            (fun position => (fiberTuple assignment 0 directions (seedOrder position)).1)
            (mixedFieldAffine (assignmentFiber assignment 1).card base
              (fiberTuple assignment 1 directions))) ≤
          constant * inputOneHigh grade 4 base directions := by
  obtain ⟨constant, nonneg, bound⟩ := seedTransferCoreDerivative_uniform_bound
    parameters grade order reference insideR seedPatch compact insidePatch
  refine ⟨constant, nonneg, fun base directions member assignment seedOrder => ?_⟩
  have cardLe : (assignmentFiber assignment 0).card ≤ order :=
    (Finset.card_le_univ _).trans (by rw [Fintype.card_fin])
  have seedEstimate := bound _ cardLe base.1 member
    (fun position => fiberTuple assignment 0 directions (seedOrder position))
    (mixedFieldAffine (assignmentFiber assignment 1).card base (fiberTuple assignment 1 directions))
  rw [Equiv.prod_comp seedOrder (fun position => directionNorm 4 (fiberTuple assignment 0 directions position))]
    at seedEstimate
  change originalGradeNorm grade _ ≤ constant *
    (∏ position, directionNorm 4 (directions (fiberEnumeration assignment 0 position))) *
      originalGradeNorm grade _ at seedEstimate
  rw [prod_fiber_eq assignment 0 (fun position => directionNorm 4 (directions position))] at seedEstimate
  conv at seedEstimate => rhs; rw [assignmentFiber_zero_eq_compl_one]
  apply seedEstimate.trans
  calc
    _ ≤ (constant * ∏ position ∈ (assignmentFiber assignment 1)ᶜ, directionNorm 4 (directions position)) *
        inputOneHigh grade 4 base (fiberTuple assignment 1 directions) :=
      mul_le_mul_of_nonneg_left (mixedFieldAffine_bound grade _ base (fiberTuple assignment 1 directions))
        (mul_nonneg nonneg (Finset.prod_nonneg fun _ _ => directionNorm_nonneg _ _))
    _ = constant * (inputOneHigh grade 4 base (fiberTuple assignment 1 directions) *
        ∏ position ∈ (assignmentFiber assignment 1)ᶜ, directionNorm 4 (directions position)) := by ring
    _ ≤ constant * inputOneHigh grade 4 base directions :=
      mul_le_mul_of_nonneg_left
        (inputOneHigh_fiber_mul_compl_le grade 4 base assignment 1 directions) nonneg

end Grad.MixedQuotientComposition
