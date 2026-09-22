import AJM4ExactOriginalSolvedGraphConsumer
import AKE4SolvedFiveBlockInverse
import AJX2OriginalFullGraphObservation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
open Set
namespace Grad.AnnularFullGraph

/-- A continuous recovery map makes the observed closed graph closed.
Recovery is required only on the genuine equation graph. -/
theorem closedObservedGraph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (observe : X → Y) (recover : Y → X) (continuousObserve : Continuous observe)
    (continuousRecover : Continuous recover) (graph : Set X) (closed : IsClosed graph)
    (same : ∀ point ∈ graph, recover (observe point) = point) : IsClosed (observe '' graph) := by
  have image : observe '' graph = recover ⁻¹' graph ∩ {point | observe (recover point) = point} := by
    ext point
    constructor
    · rintro ⟨source,inside,rfl⟩
      refine ⟨?_, congrArg observe (same source inside)⟩
      change recover (observe source) ∈ graph
      simpa only [same source inside] using inside
    · rintro ⟨inside,equality⟩
      exact ⟨recover point,inside,equality⟩
  rw [image]
  exact (closed.preimage continuousRecover).inter
    (isClosed_eq (continuousObserve.comp continuousRecover) continuous_id)

end Grad.AnnularFullGraph
