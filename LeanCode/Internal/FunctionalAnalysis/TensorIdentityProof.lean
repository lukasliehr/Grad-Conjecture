import TensorIdentityInterface
import TensorCoefficientsIdentityProof

open Grad.PDEBootstrap Grad.KernelArrays

namespace Grad.TensorAction.Identity

theorem coefficient_refl : coefficientIdentityGoal := by
  intro input output
  change (Pi.single output 1 : Fin 2 → ℝ) input = if input = output then 1 else 0
  exact Pi.single_apply output 1 input

theorem covectorMixing_refl (rank : ℕ) (field : OrderedFields rank) :
    covectorMixing rank (LinearIsometryEquiv.refl ℝ Spatial) field = field := by
  have coefficients :
      OrthogonalCoefficients.coefficient (LinearIsometryEquiv.refl ℝ Spatial) =
        TensorCoefficients.Identity.identityCoefficients := by
    funext input output
    exact coefficient_refl input output
  apply PiLp.ext
  intro output
  change (∑ input, TensorCoefficients.tensorCoefficient rank
      (OrthogonalCoefficients.coefficient (LinearIsometryEquiv.refl ℝ Spatial))
        output input • field input) = field output
  rw [coefficients]
  simp [TensorCoefficients.Identity.tensorCoefficient_identity, ite_smul]

theorem covectorLinear_refl (rank : ℕ) :
    Linear.covectorLinear rank (LinearIsometryEquiv.refl ℝ Spatial) =
      LinearMap.id (R := ℂ) (M := OrderedFields rank) := by
  apply LinearMap.ext
  intro field
  exact covectorMixing_refl rank field

end Grad.TensorAction.Identity
