import SP1Interface

noncomputable section

open Grad.PDEBootstrap
open scoped BigOperators ContDiff

namespace Grad.RepresentedKernel.SpatialProduct

theorem chainFactor_eq (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (word target : Word rank) :
    chainFactor rank orthogonal word target =
      ∏ position, orthogonal (spatialDirection (word position)) (target position) := rfl

theorem twisted_expansion {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (rank : ℕ) (word : Word rank) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (function : Spatial → Value) (point : Spatial) :
    twistedDerivative rank word orthogonal function point =
      ∑ target : Word rank, chainFactor rank orthogonal word target •
        wordDerivative rank target function (orthogonal point) := by
  let derivative := iteratedFDeriv ℝ rank function (orthogonal point)
  calc
    _ = derivative (fun position => ∑ coordinate : Fin 2,
        orthogonal (spatialDirection (word position)) coordinate • spatialDirection coordinate) := by
      apply congrArg derivative
      funext position
      exact Grad.OrthogonalCoefficients.Composition.spatialDirection_expansion _
    _ = ∑ target : Word rank, derivative (fun position =>
        orthogonal (spatialDirection (word position)) (target position) • spatialDirection (target position)) :=
      derivative.toMultilinearMap.map_sum _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro target _
      exact derivative.toMultilinearMap.map_smul_univ _ _

theorem word_chain {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (domain : Set Spatial) (openDomain : IsOpen domain) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : Grad.KernelPullback.Domain.Invariant domain orthogonal)
    (function : Spatial → Value) (rank : ℕ) (word : Word rank)
    (point : Spatial) (inside : point ∈ domain) :
    wordDerivative rank word (fun source => function (orthogonal source)) point =
      twistedDerivative rank word orthogonal function point := by
  have imageInside : orthogonal point ∈ domain := (invariant point).mpr inside
  have preimage : orthogonal ⁻¹' domain = domain := Set.ext invariant
  have chain := orthogonal.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right function
    openDomain.uniqueDiffOn imageInside rank
  rw [show orthogonal.toContinuousLinearEquiv ⁻¹' domain = domain from preimage,
    iteratedFDerivWithin_of_isOpen rank openDomain inside] at chain
  change iteratedFDeriv ℝ rank (fun source => function (orthogonal source)) point =
    (iteratedFDerivWithin ℝ rank function domain (orthogonal point)).compContinuousLinearMap
      (fun _ => orthogonal.toContinuousLinearEquiv.toContinuousLinearMap) at chain
  rw [iteratedFDerivWithin_of_isOpen rank openDomain imageInside] at chain
  exact congrArg (fun derivative => derivative (fun position => spatialDirection (word position))) chain

theorem chain : ChainGoal := by
  refine ⟨chainFactor_eq, ?_⟩
  intro Value _ _ domain openDomain orthogonal invariant function _ rank word point inside
  exact ⟨word_chain domain openDomain orthogonal invariant function rank word point inside,
    twisted_expansion rank word orthogonal function point⟩

end Grad.RepresentedKernel.SpatialProduct
