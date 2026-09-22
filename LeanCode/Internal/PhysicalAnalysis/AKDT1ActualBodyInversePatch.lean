import AKDQ33ActualAmbientMHSFields

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace Grad.PhysicalGeometry
open Grad.MainTarget Grad.PhysicalAmbient

/-- Compact separation supplies an actual inverse patch which recognizes
membership in the SAME closed physical body. No global collar injectivity
or assumed body-interior identification is required. -/
theorem exists_body_inverse_patch (position : Reference → Vec)
    (embedding : Topology.IsEmbedding position) (positionLift : Vec → Vec)
    (domain : Set Vec) (domainOpen : IsOpen domain) (contains : cylinder ⊆ domain)
    (smooth : ContDiffOn ℝ ∞ positionLift domain)
    (same : ∀ argument : ClosedDisk × ℝ,
      positionLift (referenceCoverPoint argument) = position (referenceCover argument))
    (argument : ClosedDisk × ℝ)
    (injective : Function.Injective (fderiv ℝ positionLift (referenceCoverPoint argument))) :
    ∃ patch : OpenPartialHomeomorph Vec Vec,
      (patch : Vec → Vec) = positionLift ∧ referenceCoverPoint argument ∈ patch.source ∧
      patch.source ⊆ domain ∧ ContDiffOn ℝ ∞ (patch.symm : Vec → Vec) patch.target ∧
      ∃ neighborhood : Set Vec, IsOpen neighborhood ∧ positionLift (referenceCoverPoint argument) ∈ neighborhood ∧
        neighborhood ⊆ patch.target ∧
        ∀ point ∈ neighborhood, (point ∈ range position ↔ patch.symm point ∈ cylinder) := by
  classical
  obtain ⟨patch, patchSame, patchIn, patchDomain, patchSmooth⟩ :=
    exists_smooth_inverse_patch positionLift domain domainOpen smooth (referenceCoverPoint argument)
      (contains (referenceCoverPoint_mem argument)) injective
  let sourceNeighborhood := referenceCoverPoint ⁻¹' patch.source
  have sourceOpen : IsOpen sourceNeighborhood := patch.open_source.preimage referenceCoverPoint_continuous
  let referenceNeighborhood := referenceCover '' sourceNeighborhood
  have referenceOpen : IsOpen referenceNeighborhood := referenceCover_isOpenMap _ sourceOpen
  have referenceIn : referenceCover argument ∈ referenceNeighborhood := ⟨argument, patchIn, rfl⟩
  have excludedClosed : IsClosed (position '' referenceNeighborhoodᶜ) :=
    ((reference_isCompact.of_isClosed_subset referenceOpen.isClosed_compl (subset_univ _)).image embedding.continuous).isClosed
  let neighborhood := patch.target ∩ (position '' referenceNeighborhoodᶜ)ᶜ
  have neighborhoodOpen : IsOpen neighborhood := patch.open_target.inter excludedClosed.isOpen_compl
  have imageIn : positionLift (referenceCoverPoint argument) ∈ neighborhood := by
    constructor
    · simpa only [patchSame] using patch.map_source patchIn
    · rw [same]
      rintro ⟨other, outside, equal⟩
      have otherSame : other = referenceCover argument := embedding.injective equal
      exact outside (otherSame ▸ referenceIn)
  refine ⟨patch, patchSame, patchIn, patchDomain, patchSmooth, neighborhood, neighborhoodOpen,
    imageIn, inter_subset_left, ?_⟩
  intro point pointIn
  constructor
  · rintro ⟨reference, rfl⟩
    have referenceIn : reference ∈ referenceNeighborhood := by
      by_contra outside
      exact pointIn.2 ⟨reference, outside, rfl⟩
    obtain ⟨lifted, liftedIn, liftedSame⟩ := referenceIn
    have positionIdentity : patch (referenceCoverPoint lifted) = position reference := by
      rw [patchSame, same, liftedSame]
    rw [← positionIdentity, patch.left_inv liftedIn]
    exact referenceCoverPoint_mem lifted
  · intro inverseIn
    let lifted : ClosedDisk × ℝ := (⟨planarPart (patch.symm point), inverseIn⟩, (patch.symm point) 2)
    have liftedSame : referenceCoverPoint lifted = patch.symm point := by
      ext coordinate
      fin_cases coordinate <;>
        simp [referenceCoverPoint, lifted, Grad.MainAssembly.PhysicalNormalHessian.coordinateDirection, planarPart, vector]
    refine ⟨referenceCover lifted, ?_⟩
    rw [← same, liftedSame, ← patchSame]
    exact patch.right_inv pointIn.1

end Grad.PhysicalGeometry
