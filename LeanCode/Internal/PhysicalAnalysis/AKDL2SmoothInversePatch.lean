import AKDL1ClosedSmoothExtension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace Grad.PhysicalAmbient
open Grad.MainTarget

/-- A genuine inverse patch with a smooth inverse on one open target.  The
source lies in the supplied original smooth neighborhood. -/
theorem exists_smooth_inverse_patch
    (mapping : Vec → Vec) (domain : Set Vec) (domainOpen : IsOpen domain)
    (smooth : ContDiffOn ℝ ∞ mapping domain) (point : Vec) (pointIn : point ∈ domain)
    (injective : Function.Injective (fderiv ℝ mapping point)) :
    ∃ patch : OpenPartialHomeomorph Vec Vec,
      (patch : Vec → Vec) = mapping ∧ point ∈ patch.source ∧
      patch.source ⊆ domain ∧ ContDiffOn ℝ ∞ (patch.symm : Vec → Vec) patch.target := by
  let derivative := fderiv ℝ mapping point
  have bijective : Function.Bijective derivative :=
    ⟨injective, LinearMap.injective_iff_surjective.mp injective⟩
  let inverseDerivative : Vec ≃L[ℝ] Vec := ContinuousLinearEquiv.ofBijective derivative
    (LinearMap.ker_eq_bot.mpr bijective.1) (LinearMap.range_eq_top.mpr bijective.2)
  have derivativeSame : (inverseDerivative : Vec →L[ℝ] Vec) = derivative := by
    exact ContinuousLinearEquiv.coe_ofBijective _ _ _
  have pointSmooth : ContDiffAt ℝ ∞ mapping point :=
    smooth.contDiffAt (domainOpen.mem_nhds pointIn)
  have pointDerivative : HasFDerivAt mapping (inverseDerivative : Vec →L[ℝ] Vec) point := by
    rw [derivativeSame]
    exact (pointSmooth.differentiableAt (by simp)).hasFDerivAt
  have strict := pointSmooth.hasStrictFDerivAt' pointDerivative (by simp)
  let initial := strict.toOpenPartialHomeomorph mapping
  have initialSame : (initial : Vec → Vec) = mapping := rfl
  have initialIn : point ∈ initial.source := strict.mem_toOpenPartialHomeomorph_source
  have derivativeContinuous : ContinuousOn (fderiv ℝ mapping) domain :=
    (smooth.fderiv_of_isOpen (m := ∞) domainOpen (by simp)).continuousOn
  let valid := domain ∩ {argument | IsUnit (fderiv ℝ mapping argument)}
  have validOpen : IsOpen valid := by
    apply isOpen_iff_mem_nhds.mpr
    rintro argument ⟨argumentIn, unitIn⟩
    exact inter_mem (domainOpen.mem_nhds argumentIn)
      ((derivativeContinuous.continuousAt (domainOpen.mem_nhds argumentIn)).eventually
        (Units.isOpen.mem_nhds unitIn))
  have validIn : point ∈ valid :=
    ⟨pointIn, ContinuousLinearMap.isUnit_iff_bijective.mpr bijective⟩
  let patch := initial.restr valid
  have patchSame : (patch : Vec → Vec) = mapping := rfl
  have patchIn : point ∈ patch.source := by
    exact ⟨initialIn, validOpen.interior_eq.symm ▸ validIn⟩
  refine ⟨patch, patchSame, patchIn, ?_, ?_⟩
  · intro argument argumentIn
    exact (interior_subset argumentIn.2).1
  · intro argument argumentIn
    have inverseIn := patch.map_target argumentIn
    have originalIn : patch.symm argument ∈ domain :=
      (interior_subset inverseIn.2).1
    have unitIn : IsUnit (fderiv ℝ mapping (patch.symm argument)) :=
      (interior_subset inverseIn.2).2
    have invertible := ContinuousLinearMap.isUnit_iff_bijective.mp unitIn
    let derivativeEquiv : Vec ≃L[ℝ] Vec := ContinuousLinearEquiv.ofBijective
      (fderiv ℝ mapping (patch.symm argument))
      (LinearMap.ker_eq_bot.mpr invertible.1) (LinearMap.range_eq_top.mpr invertible.2)
    have derivativeEquivSame : (derivativeEquiv : Vec →L[ℝ] Vec) =
        fderiv ℝ mapping (patch.symm argument) := by
      exact ContinuousLinearEquiv.coe_ofBijective _ _ _
    have localSmooth := smooth.contDiffAt (domainOpen.mem_nhds originalIn)
    apply (patch.contDiffAt_symm argumentIn (f₀' := derivativeEquiv) ?_ ?_).contDiffWithinAt
    · rw [patchSame, derivativeEquivSame]
      exact (localSmooth.differentiableAt (by simp)).hasFDerivAt
    · rw [patchSame]
      exact localSmooth

end Grad.PhysicalAmbient
