import SampledGlobalEmbeddingConsumer
import Mathlib.Geometry.Manifold.PartitionOfUnity

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace Grad.PhysicalAmbient

open Grad.MainTarget

/-- Smooth local extensions along a closed physical body glue to an actual
ambient smooth function with the same values on that body. -/
theorem exists_smooth_extension_of_closed
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (body : Set Vec) (bodyClosed : IsClosed body) (field : Vec → Target)
    (localExtensions : HasLocalExtensions .smooth field body) :
    ∃ extension : Vec → Target,
      ContDiff ℝ ∞ extension ∧ EqOn extension field body := by
  classical
  let constraints : Vec → Set Target := fun point =>
    if point ∈ body then {field point} else univ
  have constraintsConvex (point : Vec) : Convex ℝ (constraints point) := by
    by_cases membership : point ∈ body
    · simp [constraints, membership, convex_singleton]
    · simp [constraints, membership, convex_univ]
  have localChoice (point : Vec) :
      ∃ neighborhood ∈ 𝓝 point, ∃ extension : Vec → Target,
        ContMDiffOn 𝓘(ℝ, Vec) 𝓘(ℝ, Target) ∞ extension neighborhood ∧
        ∀ argument ∈ neighborhood, extension argument ∈ constraints argument := by
    by_cases membership : point ∈ body
    · obtain ⟨neighborhood, neighborhoodOpen, pointIn, extension, smooth, agrees⟩ :=
        localExtensions point membership
      refine ⟨neighborhood, neighborhoodOpen.mem_nhds pointIn, extension,
        smooth.contMDiffOn, ?_⟩
      intro argument argumentIn
      by_cases argumentBody : argument ∈ body
      · simpa [constraints, argumentBody] using agrees ⟨argumentIn, argumentBody⟩
      · simp [constraints, argumentBody]
    · refine ⟨bodyᶜ, bodyClosed.isOpen_compl.mem_nhds membership,
        fun _ => 0, contMDiffOn_const, ?_⟩
      intro argument argumentIn
      simp [constraints, show argument ∉ body from argumentIn]
  obtain ⟨extension, satisfies⟩ := exists_contMDiffMap_forall_mem_convex_of_local
    𝓘(ℝ, Vec) constraintsConvex localChoice
  refine ⟨extension, extension.contMDiff.contDiff, ?_⟩
  intro point pointIn
  simpa [constraints, pointIn] using satisfies point

/-- The gluing construction supplies exactly the target's `SmoothNear`
predicate and preserves every physical value on the closed body. -/
theorem exists_smoothNear_extension_of_closed
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (body : Set Vec) (bodyClosed : IsClosed body) (field : Vec → Target)
    (localExtensions : HasLocalExtensions .smooth field body) :
    ∃ extension : Vec → Target,
      SmoothNear body extension ∧ EqOn extension field body := by
  obtain ⟨extension, smooth, agrees⟩ :=
    exists_smooth_extension_of_closed body bodyClosed field localExtensions
  exact ⟨extension, ⟨univ, isOpen_univ, subset_univ _, smooth.contDiffOn⟩, agrees⟩

end Grad.PhysicalAmbient
