import WeakPullbackProof
import OC2CoefficientComposition

noncomputable section

open LineDeriv Grad.PDEBootstrap

namespace Grad.WeakPullback.Ordered

def orderedDerivative (rank : ℕ) (word : Fin rank → Fin 2)
    (distribution : FieldDistribution) : FieldDistribution :=
  iteratedLineDerivOp (fun position => spatialDirection (word position)) distribution

theorem orderedDerivative_zero (word : Fin 0 → Fin 2) (distribution : FieldDistribution) :
    orderedDerivative 0 word distribution = distribution := rfl

theorem orderedDerivative_one (word : Fin 1 → Fin 2) (distribution : FieldDistribution) :
    orderedDerivative 1 word distribution = distributionDerivative (word 0) distribution := rfl

theorem orderedDerivative_succ (rank : ℕ) (word : Fin (rank + 1) → Fin 2)
    (distribution : FieldDistribution) :
    orderedDerivative (rank + 1) word distribution =
      lineDerivOp (spatialDirection (word 0))
        (orderedDerivative rank (Fin.tail word) distribution) := rfl

def ChainGoal : Prop :=
  ∀ (rank : ℕ) (word : Fin rank → Fin 2) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (distribution : FieldDistribution),
    orderedDerivative rank word (distributionPullback orthogonal distribution) =
      ∑ input : Fin rank → Fin 2,
        (∏ position : Fin rank,
          orthogonal (spatialDirection (word position)) (input position)) •
        distributionPullback orthogonal (orderedDerivative rank input distribution)

def RankOneGoal : Prop :=
  ∀ (output : Fin 2) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (distribution : FieldDistribution),
    distributionDerivative output (distributionPullback orthogonal distribution) =
      ∑ input : Fin 2, orthogonal (spatialDirection output) input •
        distributionPullback orthogonal (distributionDerivative input distribution)

theorem interfaceConsumer (chain : ChainGoal) :
    ∀ (rank : ℕ) (word : Fin rank → Fin 2) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
      (distribution : FieldDistribution),
      iteratedLineDerivOp (fun position : Fin rank => spatialDirection (word position))
          (distributionPullback orthogonal distribution) =
        ∑ input : Fin rank → Fin 2,
          (∏ position : Fin rank,
            orthogonal (spatialDirection (word position)) (input position)) •
          distributionPullback orthogonal
            (iteratedLineDerivOp (fun position : Fin rank => spatialDirection (input position))
              distribution) := chain

end Grad.WeakPullback.Ordered
