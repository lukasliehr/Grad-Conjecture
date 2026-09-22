import QY31ActualInnerBound
import QYP1CompletedCoordinates

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 600000

namespace Grad.PhysicalCoordinates

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.MixedQuotientComposition

/-- Concrete coordinate-correct inner one-high bound, with no additional
loss. Only the vector transfer is permuted; its original norm is identical. -/
theorem physicalMixedReferenceExpression_bound
    (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade order : ℕ)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) (curvatureBound : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : Input parameters) (directions : Fin order → Input parameters),
        base.1 ∈ seedPatch → ‖base.2.1‖ ≤ curvatureBound → ChartAxisCondition base.2.2 →
        stateNorm grade
          (referenceScalar order base.2 (fun position => (directions position).2),
            q23MixedRootSeedField parameters order base directions +
              q23MixedTangentAffine parameters order base directions +
              toPhysicalCore parameters (q23MixedTransferredVector parameters reference insideR order base directions),
            q23SeedScalarDirectionalCoreDerivative parameters order base.1
              (fun position => (directions position).1) +
              q23MixedPotentialAffine parameters order base directions) ≤
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
  rw [← toPhysicalCore_norm parameters grade
    (q23MixedTransferredVector parameters reference insideR order base directions)] at transferEstimate
  have scalarEstimate := scalarBound base member directions Fin.revPerm
  change originalGradeNorm grade (q23SeedScalarDirectionalCoreDerivative parameters order base.1
    (fun position => (directions position).1)) ≤ scalarC * inputOneHigh grade 4 base directions at scalarEstimate
  have potentialEstimate := mixedPotentialAffine_bound grade order base directions
  rw [← q23MixedPotentialAffine_eq] at potentialEstimate
  have vectorTriangle := originalGradeNorm_add_le grade
    (q23MixedRootSeedField parameters order base directions + q23MixedTangentAffine parameters order base directions)
    (toPhysicalCore parameters (q23MixedTransferredVector parameters reference insideR order base directions))
  have vectorEstimate := (vectorTriangle.trans
    (add_le_add (originalGradeNorm_add_le grade _ _) le_rfl)).trans
      (add_le_add (add_le_add rootEstimate tangentEstimate) transferEstimate)
  have potentialTotal := (originalGradeNorm_add_le grade
    (q23SeedScalarDirectionalCoreDerivative parameters order base.1 (fun position => (directions position).1))
    (q23MixedPotentialAffine parameters order base directions)).trans
      (add_le_add scalarEstimate potentialEstimate)
  exact (add_le_add (add_le_add curvatureEstimate vectorEstimate) potentialTotal).trans_eq (by
    ring)

end Grad.PhysicalCoordinates

