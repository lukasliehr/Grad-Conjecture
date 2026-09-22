import GC1Proof
import MixingNorm
import TensorCoefficientsProof
import OC1RowOrthogonality
import TensorCoefficientsCompositionProof
import OC2CoefficientComposition
import TensorCoefficientsIdentityProof

noncomputable section

open Grad.PDEBootstrap
open Grad.GenericCarriers (Tensor)
open scoped BigOperators

namespace Grad.TensorAction.Generic

universe valueUniverse

variable (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]

def covectorAction (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (tensor : Tensor rank Value) : Tensor rank Value :=
  WithLp.toLp 2 (fun output => ∑ input,
    (TensorCoefficients.tensorCoefficient rank (OrthogonalCoefficients.coefficient orthogonal)
      output input : ℂ) • tensor input)

def ConstructorGoal : Prop :=
  ∀ (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial),
    ∃ equivalence : Tensor rank Value ≃ₗᵢ[ℂ] Tensor rank Value,
      (∀ tensor output, equivalence tensor output = ∑ input : Fin rank → Fin 2,
        ((∏ position : Fin rank,
          orthogonal (spatialDirection (output position)) (input position)) : ℂ) • tensor input) ∧
      (∀ tensor output, equivalence.symm tensor output = ∑ input : Fin rank → Fin 2,
        ((∏ position : Fin rank,
          orthogonal.symm (spatialDirection (output position)) (input position)) : ℂ) • tensor input)

def NormGoal : Prop :=
  ∀ (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (tensor : Tensor rank Value),
    ‖covectorAction Value rank orthogonal tensor‖ = ‖tensor‖

def CompositionGoal : Prop :=
  ∀ (rank : ℕ) (first second : Spatial ≃ₗᵢ[ℝ] Spatial) (tensor : Tensor rank Value),
    covectorAction Value rank (first.trans second) tensor =
      covectorAction Value rank first (covectorAction Value rank second tensor)

def ZeroGoal : Prop :=
  ∀ (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (tensor : Tensor 0 Value),
    covectorAction Value 0 orthogonal tensor = tensor

def BlockGoal : Prop := ConstructorGoal Value ∧ NormGoal Value ∧ CompositionGoal Value ∧ ZeroGoal Value

end Grad.TensorAction.Generic
