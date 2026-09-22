import ArrayPullback
import MixingInterface
import TensorCoefficientsInterface
import GradOrthogonalCoefficientsInterface

noncomputable section

open Grad.PDEBootstrap Grad.KernelArrays

namespace Grad.TensorAction

def covectorMixing (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (field : OrderedFields rank) : OrderedFields rank :=
  HilbertMixing.mix (fun input output =>
    TensorCoefficients.tensorCoefficient rank (OrthogonalCoefficients.coefficient orthogonal)
      output input) field

def normGoal : Prop :=
  ∀ (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : OrderedFields rank),
    ‖covectorMixing rank orthogonal field‖ = ‖field‖

def literalConsumerGoal : Prop :=
  ∀ (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : OrderedFields rank),
    ‖(WithLp.toLp 2 (fun output : Fin rank → Fin 2 =>
      ∑ input : Fin rank → Fin 2,
        (∏ position : Fin rank, orthogonal (spatialDirection (output position)) (input position)) •
          field input) : OrderedFields rank)‖ = ‖field‖

#check covectorMixing
#check normGoal
#check literalConsumerGoal
#check (rfl : normGoal = literalConsumerGoal)
#check sq_eq_sq₀

end Grad.TensorAction
