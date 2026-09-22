import QY30TransferAllocationBound
import QY29SeedScalarCoreBound
import Q23MixedInnerFamily

noncomputable section

set_option maxRecDepth 4000
set_option maxHeartbeats 1200000

open scoped BigOperators

namespace Grad.MixedQuotientComposition

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds

theorem q23MixedTangentAffine_eq (parameters : PhaseParameters) (order : ℕ)
    (base : Input parameters) (directions : Fin order → Input parameters) :
    q23MixedTangentAffine parameters order base directions = mixedTangentAffine order base directions := by
  rcases order with _ | _ | order <;> rfl

theorem q23MixedVectorAffine_eq (parameters : PhaseParameters) (order : ℕ)
    (base : Input parameters) (directions : Fin order → Input parameters) :
    q23MixedVectorAffine parameters order base directions = mixedFieldAffine order base directions := by
  rcases order with _ | _ | order <;> rfl

theorem q23MixedPotentialAffine_eq (parameters : PhaseParameters) (order : ℕ)
    (base : Input parameters) (directions : Fin order → Input parameters) :
    q23MixedPotentialAffine parameters order base directions = mixedPotentialAffine order base directions := by
  rcases order with _ | _ | order <;> rfl

theorem q23MixedRootSeedField_bound
    (parameters : PhaseParameters) (grade order : ℕ)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : Input parameters) (directions : Fin order → Input parameters),
        base.1 ∈ seedPatch → ChartAxisCondition base.2.2 →
        originalGradeNorm grade (q23MixedRootSeedField parameters order base directions) ≤
          constant * inputOneHigh grade 4 base directions := by
  obtain ⟨constant, nonneg, bound⟩ := mixedRootSeedTerm_bound
    parameters grade order seedPatch compact insidePatch
  refine ⟨(Fintype.card (Fin order → Fin 2) : ℝ) * constant, by positivity,
    fun base directions member axis => ?_⟩
  unfold q23MixedRootSeedField
  apply (originalGradeNorm_sum_le grade _ _).trans
  calc
    _ ≤ ∑ _assignment : Fin order → Fin 2, constant * inputOneHigh grade 4 base directions := by
      apply Finset.sum_le_sum
      intro assignment _
      exact bound base directions member axis assignment Fin.revPerm
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem q23MixedTransferredVector_bound
    (parameters : PhaseParameters) (grade order : ℕ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : Input parameters) (directions : Fin order → Input parameters),
        base.1 ∈ seedPatch →
        originalGradeNorm grade (q23MixedTransferredVector parameters reference insideR order base directions) ≤
          constant * inputOneHigh grade 4 base directions := by
  obtain ⟨constant, nonneg, bound⟩ := mixedTransferTerm_bound
    parameters grade order reference insideR seedPatch compact insidePatch
  refine ⟨(Fintype.card (Fin order → Fin 2) : ℝ) * constant, by positivity,
    fun base directions member => ?_⟩
  unfold q23MixedTransferredVector
  apply (originalGradeNorm_sum_le grade _ _).trans
  calc
    _ ≤ ∑ _assignment : Fin order → Fin 2, constant * inputOneHigh grade 4 base directions := by
      apply Finset.sum_le_sum
      intro assignment _
      rw [q23MixedVectorAffine_eq]
      exact bound base directions member assignment Fin.revPerm
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- The genuine Q23 inner-family one-high estimate, proved component by
component for the actual moving reference chart. It has no derivative
estimate hypothesis and incurs no loss: input and output are both grade q. -/
theorem q23MixedReferenceFamily_bound
    (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade order : ℕ)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) (curvatureBound : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : Input parameters) (directions : Fin order → Input parameters),
        base.1 ∈ seedPatch → ‖base.2.1‖ ≤ curvatureBound → ChartAxisCondition base.2.2 →
        stateNorm grade (q23MixedReferenceFamily parameters reference insideR order base directions) ≤
          constant * inputOneHigh grade 4 base directions := by
  obtain ⟨rootC, rootNonneg, rootBound⟩ := q23MixedRootSeedField_bound
    parameters grade order seedPatch compact insidePatch
  obtain ⟨tangentC, tangentNonneg, tangentBound⟩ := mixedTangentAffine_bound (parameters := parameters) grade order
  obtain ⟨transferC, transferNonneg, transferBound⟩ := q23MixedTransferredVector_bound
    parameters grade order reference insideR seedPatch compact insidePatch
  obtain ⟨scalarC, scalarNonneg, scalarBound⟩ := seedScalarCoreDerivative_mixed_bound
    parameters grade order seedPatch compact insidePatch
  refine ⟨(1 + |curvatureBound|) + rootC + tangentC + transferC + scalarC + 1,
    by positivity, fun base directions member curvature axis => ?_⟩
  have curvatureEstimate := referenceScalar_mixed_bound grade 4 order curvatureBound base directions curvature
  have rootEstimate := rootBound base directions member axis
  have tangentEstimate := tangentBound base directions
  rw [← q23MixedTangentAffine_eq] at tangentEstimate
  have transferEstimate := transferBound base directions member
  have scalarEstimate := scalarBound base member directions Fin.revPerm
  change originalGradeNorm grade (q23SeedScalarDirectionalCoreDerivative parameters order base.1
    (fun position => (directions position).1)) ≤ scalarC * inputOneHigh grade 4 base directions at scalarEstimate
  have potentialEstimate := mixedPotentialAffine_bound grade order base directions
  rw [← q23MixedPotentialAffine_eq] at potentialEstimate
  have vectorTriangle := originalGradeNorm_add_le grade
    (q23MixedRootSeedField parameters order base directions + q23MixedTangentAffine parameters order base directions)
    (q23MixedTransferredVector parameters reference insideR order base directions)
  have vectorEstimate := (vectorTriangle.trans
    (add_le_add (originalGradeNorm_add_le grade _ _) le_rfl)).trans
      (add_le_add (add_le_add rootEstimate tangentEstimate) transferEstimate)
  have potentialTotal := (originalGradeNorm_add_le grade
    (q23SeedScalarDirectionalCoreDerivative parameters order base.1 (fun position => (directions position).1))
    (q23MixedPotentialAffine parameters order base directions)).trans
      (add_le_add scalarEstimate potentialEstimate)
  exact (add_le_add (add_le_add curvatureEstimate vectorEstimate) potentialTotal).trans_eq (by
    ring)

end Grad.MixedQuotientComposition
