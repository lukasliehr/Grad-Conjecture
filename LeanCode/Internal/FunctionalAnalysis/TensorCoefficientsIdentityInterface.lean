import TensorCoefficientsInterface

open scoped BigOperators

namespace Grad.TensorCoefficients.Identity

noncomputable section

def identityCoefficients (input output : Fin 2) : ℝ :=
  if input = output then 1 else 0

def coefficientIdentityGoal (rank : ℕ) : Prop :=
  ∀ output input : Fin rank → Fin 2,
    tensorCoefficient rank identityCoefficients output input =
      if input = output then 1 else 0

def universalIdentityGoal : Prop :=
  ∀ rank : ℕ, coefficientIdentityGoal rank

end

end Grad.TensorCoefficients.Identity
