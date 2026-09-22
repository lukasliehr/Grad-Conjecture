import TensorLinearMap

noncomputable section

open Grad.PDEBootstrap Grad.KernelArrays Grad.KernelPullback Grad.TensorAction

namespace Grad.TensorLift

def constructorGoal : Prop :=
  ∀ (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial),
    ∃ lift : OrderedFields rank ≃ₗᵢ[ℂ] OrderedFields rank,
      (∀ field : OrderedFields rank,
        lift field = covectorMixing rank orthogonal (entrywisePullback rank orthogonal field)) ∧
      (∀ field : OrderedFields rank,
        lift.symm field =
          covectorMixing rank orthogonal.symm (entrywisePullback rank orthogonal.symm field))

def literalConsumerGoal : Prop :=
  ∀ (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial),
    ∃ lift : OrderedFields rank ≃ₗᵢ[ℂ] OrderedFields rank,
      (∀ field : OrderedFields rank,
        lift field = WithLp.toLp 2 (fun output : Fin rank → Fin 2 =>
          ∑ input : Fin rank → Fin 2,
            (∏ position : Fin rank,
              orthogonal (spatialDirection (output position)) (input position)) •
                orthogonalPullback orthogonal (field input))) ∧
      (∀ field : OrderedFields rank,
        lift.symm field = WithLp.toLp 2 (fun output : Fin rank → Fin 2 =>
          ∑ input : Fin rank → Fin 2,
            (∏ position : Fin rank,
              orthogonal.symm (spatialDirection (output position)) (input position)) •
                orthogonalPullback orthogonal.symm (field input)))

#check constructorGoal
#check literalConsumerGoal
#check (rfl : constructorGoal = literalConsumerGoal)
#check LinearIsometryEquiv.trans
#check LinearIsometryEquiv.trans_apply
#check LinearIsometryEquiv.coe_symm_trans
#check LinearIsometryEquiv.norm_map
#check LinearIsometryEquiv.ext

end Grad.TensorLift
