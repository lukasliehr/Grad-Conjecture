import AKDL2SmoothInversePatch
import AKDL3ReferenceCover

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace Grad.PhysicalAmbient
open Grad.MainTarget

/-- Smooth ambient reconstruction for the same embedded reference field.
The only inputs are its actual real lift, the original smooth collar and
the full derivative of the original position. -/
theorem canonicalAmbientField_hasLocalExtensions
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (position : Reference → Vec) (field : Reference → Target)
    (embedding : Topology.IsEmbedding position)
    (positionLift : Vec → Vec) (fieldLift : Vec → Target)
    (domain : Set Vec) (domainOpen : IsOpen domain) (contains : cylinder ⊆ domain)
    (positionSmooth : ContDiffOn ℝ ∞ positionLift domain)
    (fieldSmooth : ContDiffOn ℝ ∞ fieldLift domain)
    (positionSame : ∀ argument : ClosedDisk × ℝ,
      positionLift (referenceCoverPoint argument) = position (referenceCover argument))
    (fieldSame : ∀ argument : ClosedDisk × ℝ,
      fieldLift (referenceCoverPoint argument) = field (referenceCover argument))
    (derivativeInjective : ∀ argument : ClosedDisk × ℝ,
      Function.Injective (fderiv ℝ positionLift (referenceCoverPoint argument))) :
    HasLocalExtensions .smooth (canonicalAmbientField position field) (range position) := by
  classical
  rintro point ⟨reference, rfl⟩
  obtain ⟨argument, argumentSame⟩ := referenceCover_surjective reference
  obtain ⟨patch, patchSame, patchIn, patchDomain, patchSmooth⟩ :=
    exists_smooth_inverse_patch positionLift domain domainOpen positionSmooth
      (referenceCoverPoint argument) (contains (referenceCoverPoint_mem argument))
      (derivativeInjective argument)
  let sourceNeighborhood := referenceCoverPoint ⁻¹' patch.source
  have sourceOpen : IsOpen sourceNeighborhood :=
    patch.open_source.preimage referenceCoverPoint_continuous
  let referenceNeighborhood := referenceCover '' sourceNeighborhood
  have referenceOpen : IsOpen referenceNeighborhood :=
    referenceCover_isOpenMap _ sourceOpen
  have referenceIn : reference ∈ referenceNeighborhood :=
    ⟨argument, patchIn, argumentSame⟩
  have excludedClosed : IsClosed (position '' referenceNeighborhoodᶜ) :=
    ((reference_isCompact.of_isClosed_subset referenceOpen.isClosed_compl
      (subset_univ _)).image embedding.continuous).isClosed
  let neighborhood := patch.target ∩ (position '' referenceNeighborhoodᶜ)ᶜ
  have neighborhoodOpen : IsOpen neighborhood :=
    patch.open_target.inter excludedClosed.isOpen_compl
  have positionIn : position reference ∈ neighborhood := by
    constructor
    · have imageIn := patch.map_source patchIn
      rw [patchSame, positionSame, argumentSame] at imageIn
      exact imageIn
    · rintro ⟨other, otherOut, same⟩
      have otherSame : other = reference := embedding.injective same
      exact otherOut (otherSame ▸ referenceIn)
  refine ⟨neighborhood, neighborhoodOpen, positionIn,
    fun target => fieldLift (patch.symm target), ?_, ?_⟩
  · exact fieldSmooth.comp (patchSmooth.mono inter_subset_left) (by
      intro target targetIn
      exact patchDomain (patch.map_target targetIn.1))
  · rintro target ⟨targetIn, ⟨other, rfl⟩⟩
    have otherIn : other ∈ referenceNeighborhood := by
      by_contra otherOut
      exact targetIn.2 ⟨other, otherOut, rfl⟩
    obtain ⟨lifted, liftedIn, liftedSame⟩ := otherIn
    have positionIdentity : patch (referenceCoverPoint lifted) = position other := by
      rw [patchSame, positionSame, liftedSame]
    have inverseIdentity : patch.symm (position other) = referenceCoverPoint lifted := by
      rw [← positionIdentity]
      exact patch.left_inv liftedIn
    change fieldLift (patch.symm (position other)) = _
    rw [inverseIdentity, fieldSame, liftedSame,
      canonicalAmbientField_apply position field embedding.injective other]

/-- A single globally smooth ambient field agrees with every original
reference value, including the axis and outer boundary. -/
theorem exists_ambient_smooth_field
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (position : Reference → Vec) (field : Reference → Target)
    (embedding : Topology.IsEmbedding position)
    (positionLift : Vec → Vec) (fieldLift : Vec → Target)
    (domain : Set Vec) (domainOpen : IsOpen domain) (contains : cylinder ⊆ domain)
    (positionSmooth : ContDiffOn ℝ ∞ positionLift domain)
    (fieldSmooth : ContDiffOn ℝ ∞ fieldLift domain)
    (positionSame : ∀ argument : ClosedDisk × ℝ,
      positionLift (referenceCoverPoint argument) = position (referenceCover argument))
    (fieldSame : ∀ argument : ClosedDisk × ℝ,
      fieldLift (referenceCoverPoint argument) = field (referenceCover argument))
    (derivativeInjective : ∀ argument : ClosedDisk × ℝ,
      Function.Injective (fderiv ℝ positionLift (referenceCoverPoint argument))) :
    ∃ ambient : Vec → Target, ContDiff ℝ ∞ ambient ∧
      ∀ point : Reference, ambient (position point) = field point := by
  have bodyClosed : IsClosed (range position) := by
    have compactBody := reference_isCompact.image embedding.continuous
    simpa using compactBody.isClosed
  obtain ⟨ambient, ambientSmooth, agrees⟩ := exists_smooth_extension_of_closed
    (range position) bodyClosed (canonicalAmbientField position field)
    (canonicalAmbientField_hasLocalExtensions position field embedding positionLift fieldLift
      domain domainOpen contains positionSmooth fieldSmooth positionSame fieldSame derivativeInjective)
  refine ⟨ambient, ambientSmooth, ?_⟩
  intro point
  rw [agrees (mem_range_self point), canonicalAmbientField_apply position field embedding.injective point]

end Grad.PhysicalAmbient
