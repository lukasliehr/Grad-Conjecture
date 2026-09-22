import Q23MixedInnerFamily

noncomputable section

open Set
open scoped BigOperators

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.Constraints
open Grad.Constraints.Gauges Grad.Constraints.Seed

theorem q23SeedFieldDirectionalCoreDerivative_zero
    (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin 0 → Seed.Parameters) :
    q23SeedFieldDirectionalCoreDerivative phase 0 parameter directions =
      tameSeedField phase parameter inside := by
  apply q23FieldEmbed_injective phase 3 0
  change q23ACoreEta phase 3 0
      (q23SeedFieldCoreDerivative phase 0 parameter
        (fun position => directions position.rev)) =
    q23ACoreEta phase 3 0 (tameSeedField phase parameter inside)
  rw [← completedTameSeedFieldFamily_all_orders_core phase 0 0 parameter inside
      (fun position => directions position.rev),
    iteratedFDeriv_zero_apply,
    completedTameSeedFieldFamily_core phase 0 parameter inside]
  rfl

theorem q23SeedScalarDirectionalCoreDerivative_zero
    (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin 0 → Seed.Parameters) :
    q23SeedScalarDirectionalCoreDerivative phase 0 parameter directions =
      tameSeedScalar phase parameter inside := by
  unfold q23SeedScalarDirectionalCoreDerivative
  apply q23FieldEmbed_injective phase 1 0
  rw [← completedTameSeedScalarFamily_all_orders_core phase 0 0 parameter inside
      (fun position => directions position.rev),
    iteratedFDeriv_zero_apply,
    completedTameSeedScalarFamily_core phase 0 parameter inside]

theorem q23SeedTransferDirectionalCoreDerivative_zero
    (phase : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin 0 → Seed.Parameters) :
    q23SeedTransferDirectionalCoreDerivative phase reference insideR
        0 parameter directions =
      seedTransfer phase reference insideR parameter inside := by
  apply LinearMap.ext
  intro field
  apply q23FieldEmbed_injective phase 3 0
  change q23ACoreEta phase 3 0
      (q23SeedTransferCoreDerivative phase reference insideR 0 parameter
        (fun position => directions position.rev) field) =
    q23ACoreEta phase 3 0
      (seedTransfer phase reference insideR parameter inside field)
  rw [← completedSeedTransferFamily_all_orders_core phase 0 reference insideR 0
      parameter inside (fun position => directions position.rev) field,
    completedSeedTransferParameterDerivative, iteratedFDeriv_zero_apply,
    q23ACoreEta_apply,
    completedSeedTransferFamily_core phase 0 reference insideR parameter inside field]
  rfl

theorem rootDerivativeFamily_of_order_eq_zero
    {phase : PhaseParameters} {order : ℕ} (equal : order = 0)
    (base : TangentCoefficient phase) (directions : Fin order → TangentCoefficient phase) :
    rootDerivativeFamily order base directions =
      tameRootShifted 0 (tangentQuadratic base) := by
  subst order
  rw [rootDerivativeFamily_zero]
  rfl

theorem q23SeedFieldDirectionalCoreDerivative_of_order_eq_zero
    (phase : PhaseParameters) {order : ℕ} (equal : order = 0)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) :
    q23SeedFieldDirectionalCoreDerivative phase order parameter directions =
      tameSeedField phase parameter inside := by
  subst order
  exact q23SeedFieldDirectionalCoreDerivative_zero phase parameter inside directions

theorem q23SeedTransferDirectionalCoreDerivative_of_order_eq_zero
    (phase : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) {order : ℕ} (equal : order = 0)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) :
    q23SeedTransferDirectionalCoreDerivative phase reference insideR order parameter directions =
      seedTransfer phase reference insideR parameter inside := by
  subst order
  exact q23SeedTransferDirectionalCoreDerivative_zero
    phase reference insideR parameter inside directions

theorem q23MixedVectorAffine_of_order_eq_zero
    (phase : PhaseParameters) {order : ℕ} (equal : order = 0)
    (base : Q23MixedInput phase) (directions : Fin order → Q23MixedInput phase) :
    q23MixedVectorAffine phase order base directions = base.2.2.2.1 := by
  subst order
  rfl

theorem q23MixedRootSeedField_zero
    (phase : PhaseParameters) (base : Q23MixedInput phase)
    (inside : base.1 ∈ Seed.parameterDomain)
    (directions : Fin 0 → Q23MixedInput phase) :
    q23MixedRootSeedField phase 0 base directions =
      tameScalarMultiplier 3
        (tameRootShifted 0 (tangentQuadratic base.2.2.1))
        (tameSeedField phase base.1 inside) := by
  have cardZero (assignment : Fin 0 → Fin 2) (slot : Fin 2) :
      (assignmentFiber assignment slot).card = 0 := by
    have empty : (Finset.univ : Finset (Fin 0)) = ∅ := Finset.univ_eq_empty
    rw [assignmentFiber, empty, Finset.filter_empty, Finset.card_empty]
  rw [q23MixedRootSeedField, Finset.univ_unique, Finset.sum_singleton]
  have rootEqual := rootDerivativeFamily_of_order_eq_zero
    (cardZero default 0) base.2.2.1
    (fun position => (q23FiberTuple default 0 directions position).2.2.1)
  have fieldEqual := q23SeedFieldDirectionalCoreDerivative_of_order_eq_zero
    phase (cardZero default 1) base.1 inside
    (fun position => (q23FiberTuple default 1 directions position).1)
  exact congrArg₂
    (fun coefficient field => tameScalarMultiplier (parameters := phase) 3 coefficient field)
    rootEqual fieldEqual

theorem q23MixedTransferredVector_zero
    (phase : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain)
    (base : Q23MixedInput phase) (inside : base.1 ∈ Seed.parameterDomain)
    (directions : Fin 0 → Q23MixedInput phase) :
    q23MixedTransferredVector phase reference insideR 0 base directions =
      seedTransfer phase reference insideR base.1 inside base.2.2.2.1 := by
  have cardZero (assignment : Fin 0 → Fin 2) (slot : Fin 2) :
      (assignmentFiber assignment slot).card = 0 := by
    have empty : (Finset.univ : Finset (Fin 0)) = ∅ := Finset.univ_eq_empty
    rw [assignmentFiber, empty, Finset.filter_empty, Finset.card_empty]
  rw [q23MixedTransferredVector, Finset.univ_unique, Finset.sum_singleton]
  have operatorEqual := q23SeedTransferDirectionalCoreDerivative_of_order_eq_zero
    phase reference insideR (cardZero default 0) base.1 inside
    (fun position => (q23FiberTuple default 0 directions position).1)
  have vectorEqual := q23MixedVectorAffine_of_order_eq_zero
    phase (cardZero default 1) base (q23FiberTuple default 1 directions)
  exact congrArg₂ (fun operator field => operator field) operatorEqual vectorEqual

/-- Zeroth level of the mixed family is the literal moving-seed inner state. -/
theorem q23MixedReferenceFamily_zero
    (phase : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain)
    (base : Q23MixedInput phase) (inside : base.1 ∈ Seed.parameterDomain)
    (directions : Fin 0 → Q23MixedInput phase) :
    q23MixedReferenceFamily phase reference insideR 0 base directions =
      referenceState phase reference insideR base.1 inside base.2 := by
  unfold q23MixedReferenceFamily referenceState normalizedChart
  rw [q23MixedRootSeedField_zero phase base inside directions,
    q23MixedTransferredVector_zero phase reference insideR base inside directions,
    q23SeedScalarDirectionalCoreDerivative_zero phase base.1 inside]
  rfl

end Grad.NonlinearQuotientBounds
