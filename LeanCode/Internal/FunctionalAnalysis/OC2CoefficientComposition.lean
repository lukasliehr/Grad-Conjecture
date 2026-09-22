import OC2CompositionInterface

open Grad.PDEBootstrap

namespace Grad.OrthogonalCoefficients.Composition

theorem spatialDirection_expansion (point : Spatial) :
    point = ∑ middle : Fin 2, point middle • spatialDirection middle := by
  simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
    spatialDirection, PiLp.single]
    using ((EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr point).symm

theorem coefficientComposition : CoefficientCompositionGoal := by
  intro first second input output
  change second (first (spatialDirection output)) input = _
  have expansion := congrArg second (spatialDirection_expansion (first (spatialDirection output)))
  rw [map_sum] at expansion
  simp only [LinearIsometryEquiv.map_smul] at expansion
  have coordinates := congrArg (EuclideanSpace.projₗ (𝕜 := ℝ) input) expansion
  rw [map_sum] at coordinates
  change second (first (spatialDirection output)) input =
    ∑ middle : Fin 2,
      (first (spatialDirection output) middle • second (spatialDirection middle)) input at coordinates
  simpa only [PiLp.smul_apply, smul_eq_mul, coefficient, mul_comm] using coordinates

end Grad.OrthogonalCoefficients.Composition
