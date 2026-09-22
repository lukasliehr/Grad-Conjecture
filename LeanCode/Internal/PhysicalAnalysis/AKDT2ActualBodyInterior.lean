import AKDT1ActualBodyInversePatch

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace Grad.PhysicalGeometry
open Grad.MainTarget Grad.PhysicalAmbient
open Grad.PhysicalFamily.SampledGlobalEmbedding Grad.MainAssembly.PhysicalNormalHessian

def actualPlanarProjection : Vec →L[ℝ] Plane :=
  LinearMap.toContinuousLinearMap
    { toFun := planarPart
      map_add' := by
        intro first second
        ext coordinate
        fin_cases coordinate <;> simp [planarPart]
      map_smul' := by
        intro scalar point
        ext coordinate
        fin_cases coordinate <;> simp [planarPart] }

@[simp] theorem actualPlanarProjection_apply (point : Vec) :
    actualPlanarProjection point = planarPart point := rfl

/-- The literal closed reference cylinder has precisely the open disk as its
interior, using the actual planar projection. -/
theorem cylinder_mem_interior_iff (point : Vec) :
    point ∈ interior cylinder ↔ ‖planarPart point‖ < 1 := by
  have onto : Function.Surjective actualPlanarProjection := by
    intro disk
    exact ⟨coordinateDirection disk 0, planarPart_coordinateDirection disk 0⟩
  have projectionOpen : IsOpenMap actualPlanarProjection := actualPlanarProjection.isOpenMap onto
  have interiors := projectionOpen.preimage_interior_eq_interior_preimage
    actualPlanarProjection.continuous (Metric.closedBall (0 : Plane) 1)
  rw [interior_closedBall] at interiors
  swap
  · norm_num
  have membership := congrArg (fun set : Set Vec => point ∈ set) interiors.symm
  simpa [cylinder, Metric.closedBall, Metric.ball, dist_zero_right] using membership

/-- Interior membership transfers through the genuine body-recognizing inverse
patch, including its boundary points. -/
theorem position_mem_interior_iff (position : Reference → Vec)
    (embedding : Topology.IsEmbedding position) (positionLift : Vec → Vec)
    (domain : Set Vec) (domainOpen : IsOpen domain) (contains : cylinder ⊆ domain)
    (smooth : ContDiffOn ℝ ∞ positionLift domain)
    (same : ∀ argument : ClosedDisk × ℝ,
      positionLift (referenceCoverPoint argument) = position (referenceCover argument))
    (argument : ClosedDisk × ℝ)
    (injective : Function.Injective (fderiv ℝ positionLift (referenceCoverPoint argument))) :
    position (referenceCover argument) ∈ interior (range position) ↔ ‖argument.1.val‖ < 1 := by
  obtain ⟨patch, patchSame, patchIn, _, _, neighborhood, neighborhoodOpen, imageIn,
    _, recognizes⟩ := exists_body_inverse_patch position embedding positionLift domain
      domainOpen contains smooth same argument injective
  have imageInPatch : patch (referenceCoverPoint argument) ∈ neighborhood := by
    simpa only [patchSame] using imageIn
  have eventualNeighborhood : ∀ᶠ point in 𝓝 (referenceCoverPoint argument), patch point ∈ neighborhood :=
    (patch.continuousAt patchIn).eventually (neighborhoodOpen.mem_nhds imageInPatch)
  have equivalent : ∀ᶠ point in 𝓝 (referenceCoverPoint argument),
      (patch point ∈ range position ↔ point ∈ cylinder) := by
    filter_upwards [patch.open_source.mem_nhds patchIn, eventualNeighborhood] with point sourceIn imageIn
    simpa only [patch.left_inv sourceIn] using recognizes (patch point) imageIn
  have neighborhoods : range position ∈ 𝓝 (patch (referenceCoverPoint argument)) ↔
      cylinder ∈ 𝓝 (referenceCoverPoint argument) := by
    rw [← patch.map_nhds_eq patchIn]
    change (∀ᶠ point in 𝓝 (referenceCoverPoint argument), patch point ∈ range position) ↔
      ∀ᶠ point in 𝓝 (referenceCoverPoint argument), point ∈ cylinder
    constructor
    · intro membership
      filter_upwards [equivalent, membership] with point equivalence pointIn
      exact equivalence.mp pointIn
    · intro membership
      filter_upwards [equivalent, membership] with point equivalence pointIn
      exact equivalence.mpr pointIn
  rw [patchSame, same] at neighborhoods
  rw [mem_interior_iff_mem_nhds, neighborhoods, ← mem_interior_iff_mem_nhds,
    cylinder_mem_interior_iff]
  rw [referenceCoverPoint, planarPart_coordinateDirection]

/-- Compactness of the SAME reference body gives its exact physical frontier. -/
theorem position_mem_frontier_iff (position : Reference → Vec)
    (embedding : Topology.IsEmbedding position) (positionLift : Vec → Vec)
    (domain : Set Vec) (domainOpen : IsOpen domain) (contains : cylinder ⊆ domain)
    (smooth : ContDiffOn ℝ ∞ positionLift domain)
    (same : ∀ argument : ClosedDisk × ℝ,
      positionLift (referenceCoverPoint argument) = position (referenceCover argument))
    (argument : ClosedDisk × ℝ)
    (injective : Function.Injective (fderiv ℝ positionLift (referenceCoverPoint argument))) :
    position (referenceCover argument) ∈ frontier (range position) ↔ ‖argument.1.val‖ = 1 := by
  have bodyClosed : IsClosed (range position) := by
    simpa only [image_univ] using (reference_isCompact.image embedding.continuous).isClosed
  rw [frontier, bodyClosed.closure_eq, Set.mem_sdiff]
  simp only [mem_range_self, true_and]
  rw [position_mem_interior_iff position embedding positionLift domain domainOpen contains smooth same argument injective]
  exact ⟨fun bound => le_antisymm argument.1.property (le_of_not_gt bound), fun equal => by simp [equal]⟩

end Grad.PhysicalGeometry
