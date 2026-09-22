import TensorCompositionInterface
import TensorCoefficientsCompositionProof
import OC2CoefficientComposition

open Grad.PDEBootstrap Grad.KernelArrays

namespace Grad.TensorAction.Composition

theorem covectorMixing_trans (rank : ℕ) (first second : Spatial ≃ₗᵢ[ℝ] Spatial)
    (field : OrderedFields rank) :
    covectorMixing rank (first.trans second) field =
      covectorMixing rank first (covectorMixing rank second field) := by
  have coefficients : OrthogonalCoefficients.coefficient (first.trans second) =
      TensorCoefficients.Composition.productCoefficients
        (OrthogonalCoefficients.coefficient first) (OrthogonalCoefficients.coefficient second) := by
    funext input output
    exact OrthogonalCoefficients.Composition.coefficientComposition first second input output
  apply PiLp.ext
  intro output
  change (∑ input, TensorCoefficients.tensorCoefficient rank
      (OrthogonalCoefficients.coefficient (first.trans second)) output input • field input) =
    ∑ middleWord, TensorCoefficients.tensorCoefficient rank
      (OrthogonalCoefficients.coefficient first) output middleWord •
        (∑ input, TensorCoefficients.tensorCoefficient rank
          (OrthogonalCoefficients.coefficient second) middleWord input • field input)
  rw [coefficients]
  simp_rw [TensorCoefficients.Composition.tensorCoefficient_composition, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp only [Finset.smul_sum, mul_smul]

theorem covectorLinear_trans (rank : ℕ) (first second : Spatial ≃ₗᵢ[ℝ] Spatial) :
    Linear.covectorLinear rank (first.trans second) =
      (Linear.covectorLinear rank first).comp (Linear.covectorLinear rank second) := by
  apply LinearMap.ext
  intro field
  exact covectorMixing_trans rank first second field

end Grad.TensorAction.Composition
