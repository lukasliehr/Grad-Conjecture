import MainStatement
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section

open Set

namespace Grad.MainAssembly.TargetReparametrization

open Grad.MainTarget

/-! Exact dependency-free target reparametrization laws used by the later
`Related` equivalence and `ModuliCurve` integration. -/

theorem identityHasRegularLocalLifts (regularity : Regularity) :
    HasRegularLocalLifts regularity (Equiv.refl Reference) := by
  intro point pointInCylinder
  have identitySmooth : ContDiff ℝ regularity.order (id : Vec → Vec) := contDiff_id
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ point, id, identitySmooth.contDiffOn, ?_⟩
  intro argument _ argumentInCylinder
  refine ⟨argumentInCylinder, ?_⟩
  rfl

/-- Exact `NG_Z06_ID`: the identity reference equivalence has identity local
lifts in both directions, at every finite or smooth target regularity. -/
theorem identityIsReparametrization (regularity : Regularity) :
    IsReparametrization regularity (Equiv.refl Reference) := by
  exact ⟨identityHasRegularLocalLifts regularity,
    identityHasRegularLocalLifts regularity⟩

/-- Exact `NG_Z06_INV`: the target predicate already stores both the forward
and inverse local-lift witnesses, so inversion swaps them without changing any
domain, regularity, or value condition. -/
theorem inverseIsReparametrization (regularity : Regularity)
    (reparametrization : Reference ≃ Reference)
    (isReparametrization : IsReparametrization regularity reparametrization) :
    IsReparametrization regularity reparametrization.symm := by
  rcases isReparametrization with ⟨forward, inverse⟩
  refine ⟨inverse, ?_⟩
  simpa using forward

end Grad.MainAssembly.TargetReparametrization
