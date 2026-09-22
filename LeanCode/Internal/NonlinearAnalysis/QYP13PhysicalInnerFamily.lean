import QYP12PhysicalInnerBound
import Q23MixedInnerZeroth
import PCO2PhysicalChartRange

noncomputable section

namespace Grad.PhysicalCoordinates

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.MixedQuotientComposition

/-- The coordinate-correct mixed inner tower. The physical permutation is
applied only to the transferred vector remainder, not to the seed field
or physical tangential field. -/
def physicalMixedInnerFamily (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (order : ℕ)
    (base : Input parameters) (directions : Fin order → Input parameters) : QuotientState parameters :=
  (referenceScalar order base.2 (fun position => (directions position).2),
    q23MixedRootSeedField parameters order base directions +
      q23MixedTangentAffine parameters order base directions +
      toPhysicalCore parameters (q23MixedTransferredVector parameters reference insideR order base directions),
    q23SeedScalarDirectionalCoreDerivative parameters order base.1
      (fun position => (directions position).1) + q23MixedPotentialAffine parameters order base directions)

theorem physicalMixedInnerFamily_zero (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (base : Input parameters)
    (insideS : base.1 ∈ Seed.parameterDomain) (directions : Fin 0 → Input parameters) :
    physicalMixedInnerFamily parameters reference insideR 0 base directions =
      physicalReferenceState parameters reference insideR base.1 insideS base.2 := by
  unfold physicalMixedInnerFamily physicalReferenceState normalizedChart
  rw [q23MixedRootSeedField_zero parameters base insideS directions,
    q23MixedTransferredVector_zero parameters reference insideR base insideS directions,
    q23SeedScalarDirectionalCoreDerivative_zero parameters base.1 insideS]
  rfl

theorem physicalMixedInnerFamily_bound (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade order : ℕ)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) (curvatureBound : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : Input parameters) (directions : Fin order → Input parameters),
        base.1 ∈ seedPatch → ‖base.2.1‖ ≤ curvatureBound → ChartAxisCondition base.2.2 →
        stateNorm grade (physicalMixedInnerFamily parameters reference insideR order base directions) ≤
          constant * inputOneHigh grade 4 base directions :=
  physicalMixedReferenceExpression_bound parameters reference insideR grade order seedPatch compact insidePatch curvatureBound

end Grad.PhysicalCoordinates
