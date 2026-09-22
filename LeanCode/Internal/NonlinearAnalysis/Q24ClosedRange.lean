import Q24DensityBounds

noncomputable section

open Filter
open scoped Topology ContDiff

namespace Grad.Q24Realization

/-- A continuous map on an open domain lands in a fixed closed target
as soon as its exact values on a dense core do. No target projection is
inserted into the map. -/
theorem mapsTo_closed_of_dense_core {C E F : Type*}
    [TopologicalSpace E] [TopologicalSpace F]
    (embedding : C → E) (dense : DenseRange embedding)
    (mapping : E → F) (domain : Set E) (target : Set F)
    (openDomain : IsOpen domain) (closedTarget : IsClosed target)
    (continuous : ContinuousOn mapping domain)
    (coreRange : ∀ core, embedding core ∈ domain → mapping (embedding core) ∈ target) :
    Set.MapsTo mapping domain target := by
  intro point inside
  by_contra outside
  have nearby := ((continuous point inside).continuousAt (openDomain.mem_nhds inside)).eventually
    (closedTarget.isOpen_compl.mem_nhds outside)
  obtain ⟨core, membership, contradiction⟩ := dense.mem_nhds
    (inter_mem (openDomain.mem_nhds inside) nearby)
  exact contradiction (coreRange core membership)

/-- The actual iterated derivative under a bounded real-linear input
restriction, on the original open domain rather than a global extension. -/
theorem iteratedFDeriv_precomp_on_open {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (input : E →L[ℝ] F) (mapping : F → G) (domain : Set F)
    (openDomain : IsOpen domain) (smooth : ContDiffOn ℝ ∞ mapping domain)
    (order : ℕ) (base : E) (inside : input base ∈ domain) (directions : Fin order → E) :
    iteratedFDeriv ℝ order (mapping ∘ input) base directions =
      iteratedFDeriv ℝ order mapping (input base) (fun position => input (directions position)) := by
  have identity := input.iteratedFDerivWithin_comp_right smooth openDomain.uniqueDiffOn
    (openDomain.preimage input.continuous).uniqueDiffOn inside
    (show (order : WithTop ℕ∞) ≤ ∞ by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  rw [iteratedFDerivWithin_of_isOpen order (openDomain.preimage input.continuous) inside,
    iteratedFDerivWithin_of_isOpen order openDomain inside] at identity
  exact congrArg (fun derivative => derivative directions) identity

end Grad.Q24Realization
