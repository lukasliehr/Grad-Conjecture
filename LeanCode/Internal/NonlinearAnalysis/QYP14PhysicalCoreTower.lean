import QYP13PhysicalInnerFamily
import QY15MixedCompositionBound

noncomputable section

open scoped BigOperators

namespace Grad.PhysicalCoordinates

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.MixedQuotientComposition

/-- The literal mixed core tower of the actual five homogeneous quotient
parts at the moving reference chart. Its derivative identification is
proved separately from the componentwise estimate. -/
def physicalMixedSliceCoreTower (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (order : ℕ) (base : Input parameters) (directions : Fin order → Input parameters) :
    QuotientRows parameters :=
  composedDerivative (physicalMixedInnerFamily parameters reference insideR) cellLength order base directions

theorem physicalMixedSliceCoreTower_zero (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (base : Input parameters) (insideS : base.1 ∈ Seed.parameterDomain)
    (directions : Fin 0 → Input parameters) :
    physicalMixedSliceCoreTower parameters cellLength reference insideR 0 base directions =
      physicalFixedSliceMap parameters cellLength reference insideR base.1 insideS base.2 := by
  rw [physicalMixedSliceCoreTower, MixedQuotientComposition.composedDerivative_zeroth,
    physicalMixedInnerFamily_zero parameters reference insideR base insideS]
  rfl

/-- The exact loss-six Q23 one-high estimate of the literal mixed core
tower. This is an unconditional estimate of the explicit actual formula,
not an estimate postulated for a replacement derivative family. -/
theorem physicalMixedSliceCoreTower_bound
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (grade order : ℕ) (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) (curvatureBound stateBound : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : Input parameters) (directions : Fin order → Input parameters),
        base.1 ∈ seedPatch → ‖base.2.1‖ ≤ curvatureBound →
        ChartAxisCondition base.2.2 → baseNorm 4 base ≤ stateBound →
        rowsGradeNorm grade (physicalMixedSliceCoreTower parameters cellLength reference insideR order base directions) ≤
          constant * inputOneHigh (grade + 6) 4 base directions := by
  let Admissible : Input parameters → Prop := fun base =>
    base.1 ∈ seedPatch ∧ ‖base.2.1‖ ≤ curvatureBound ∧ ChartAxisCondition base.2.2
  have inner : ∀ q count, ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : Input parameters) (directions : Fin count → Input parameters),
        Admissible base →
        stateNorm q (physicalMixedInnerFamily parameters reference insideR count base directions) ≤
          constant * inputOneHigh q 4 base directions := by
    intro q count
    obtain ⟨constant, nonneg, bound⟩ := physicalMixedInnerFamily_bound
      parameters reference insideR q count seedPatch compact insidePatch curvatureBound
    exact ⟨constant, nonneg, fun base directions member =>
      bound base directions member.1 member.2.1 member.2.2⟩
  obtain ⟨constant, nonneg, bound⟩ := composedDerivative_bound
    (physicalMixedInnerFamily parameters reference insideR) Admissible inner cellLength grade order stateBound
  exact ⟨constant, nonneg, fun base directions member curvature axis bounded =>
    bound base directions ⟨member, curvature, axis⟩ bounded⟩

end Grad.PhysicalCoordinates

