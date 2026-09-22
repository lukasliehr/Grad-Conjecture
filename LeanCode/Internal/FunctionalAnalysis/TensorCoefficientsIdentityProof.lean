import TensorCoefficientsIdentityInterface

open scoped BigOperators

namespace Grad.TensorCoefficients.Identity

theorem tensorCoefficient_identity (rank : ℕ)
    (output input : Fin rank → Fin 2) :
    tensorCoefficient rank identityCoefficients output input =
      if input = output then 1 else 0 := by
  classical
  unfold tensorCoefficient identityCoefficients
  simpa only [← funext_iff] using
    (Fintype.prod_boole (M₀ := ℝ)
      (p := fun position => input position = output position))

theorem universalIdentity : universalIdentityGoal :=
  tensorCoefficient_identity

end Grad.TensorCoefficients.Identity
