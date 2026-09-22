import TensorLinearMap

open Grad.PDEBootstrap Grad.KernelArrays

namespace Grad.TensorAction.Identity

def coefficientIdentityGoal : Prop :=
  ∀ (input output : Fin 2),
    OrthogonalCoefficients.coefficient (LinearIsometryEquiv.refl ℝ Spatial) input output =
      if input = output then 1 else 0

def actionIdentityGoal : Prop :=
  ∀ (rank : ℕ) (field : OrderedFields rank),
    covectorMixing rank (LinearIsometryEquiv.refl ℝ Spatial) field = field

def linearIdentityGoal : Prop :=
  ∀ (rank : ℕ),
    Linear.covectorLinear rank (LinearIsometryEquiv.refl ℝ Spatial) =
      LinearMap.id (R := ℂ) (M := OrderedFields rank)

#check coefficientIdentityGoal
#check actionIdentityGoal
#check linearIdentityGoal
#check Pi.single_apply
#check Finset.sum_ite_eq'
#check PiLp.ext
#check ite_smul
#check zero_smul
#check one_smul
#check LinearMap.ext

end Grad.TensorAction.Identity
