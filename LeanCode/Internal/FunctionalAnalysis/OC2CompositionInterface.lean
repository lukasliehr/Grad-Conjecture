import GradOrthogonalCoefficientsInterface

open Grad.PDEBootstrap

namespace Grad.OrthogonalCoefficients.Composition

def CoefficientCompositionGoal : Prop :=
  ∀ (first second : Spatial ≃ₗᵢ[ℝ] Spatial) (input output : Fin 2),
    coefficient (first.trans second) input output =
      ∑ middle : Fin 2, coefficient second input middle * coefficient first middle output

end Grad.OrthogonalCoefficients.Composition
