import AJE60OriginalSharedSourceConsumer
import AJC19OriginalSharedInverseConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter
open scoped Topology
namespace Grad.AnnularSolvedGraphDensity

section Topological
variable {Core X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (approximation : Core → X) (dense : DenseRange approximation)
    (response : X → Y) (continuousResponse : Continuous response)

include dense continuousResponse

/-- Density retains the whole datum and the whole solution graph together. -/
theorem continuousFullGraph_mem_closure (data : X) :
    (data,response data) ∈ closure (range (fun core => (approximation core,response (approximation core)))) := by
  apply isClosed_property dense
    (isClosed_closure.preimage (continuous_id.prodMk continuousResponse)) _ data
  intro core
  exact subset_closure ⟨core,rfl⟩

/-- Any continuous original graph observation receives the SAME joint limit. -/
theorem continuousFullGraph_observation_closure (observation : X × Y → Z)
    (continuousObservation : Continuous observation) (data : X) :
    observation (data,response data) ∈
      closure (range (fun core => observation (approximation core,response (approximation core)))) := by
  apply isClosed_property dense
    (isClosed_closure.preimage (continuousObservation.comp (continuous_id.prodMk continuousResponse))) _ data
  intro core
  exact subset_closure ⟨core,rfl⟩

/-- This is the later smooth-core closure step; smoothness of the solutions
must be established separately for the actual smooth-source solves. -/
theorem continuousFullGraph_closed_transfer (observation : X × Y → Z)
    (continuousObservation : Continuous observation) (closedSet : Set Z) (closed : IsClosed closedSet)
    (coreMember : ∀ core, observation (approximation core,response (approximation core)) ∈ closedSet)
    (data : X) : observation (data,response data) ∈ closedSet := by
  exact isClosed_property dense
    (closed.preimage (continuousObservation.comp (continuous_id.prodMk continuousResponse))) coreMember data

variable [T2Space Y]

omit dense in
theorem continuousFullGraph_isClosed : IsClosed (range (fun data : X => (data,response data))) := by
  have same : range (fun data : X => (data,response data)) = {point : X × Y | response point.1 = point.2} := by
    ext point
    constructor
    · rintro ⟨data,rfl⟩
      rfl
    · intro equality
      exact ⟨point.1,Prod.ext rfl equality⟩
  rw [same]
  exact isClosed_eq (continuousResponse.comp continuous_fst) continuous_snd

/-- The closure is exactly the full solved graph, with its source coordinate. -/
theorem continuousFullGraph_closure_eq :
    closure (range (fun core => (approximation core,response (approximation core)))) =
      range (fun data : X => (data,response data)) := by
  apply subset_antisymm
  · apply closure_minimal _ (continuousFullGraph_isClosed response continuousResponse)
    rintro point ⟨core,rfl⟩
    exact ⟨approximation core,rfl⟩
  · rintro point ⟨data,rfl⟩
    exact continuousFullGraph_mem_closure approximation dense response continuousResponse data
end Topological

end Grad.AnnularSolvedGraphDensity
