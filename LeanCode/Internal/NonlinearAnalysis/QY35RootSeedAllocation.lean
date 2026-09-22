import QY34MultiplierGenuine
import QY12MixedCompositionTerms

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1200000

open Filter
open scoped BigOperators Topology

namespace Grad.MixedQuotientComposition

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.NonlinearQuotientBounds

def mixedRootBlock (parameters : PhaseParameters) (order : ℕ) (base : Input parameters)
    (directions : Fin order → Input parameters) : TameCoefficient parameters :=
  rootDerivativeFamily order base.2.2.1 (fun position => (directions position).2.2.1)

def mixedSeedFieldBlock (parameters : PhaseParameters) (order : ℕ) (base : Input parameters)
    (directions : Fin order → Input parameters) : ACore parameters 3 :=
  q23SeedFieldDirectionalCoreDerivative parameters order base.1 (fun position => (directions position).1)

def mixedRootSeedTerm (parameters : PhaseParameters) {order : ℕ} (assignment : Fin order → Fin 2)
    (base : Input parameters) (directions : Fin order → Input parameters) : ACore parameters 3 :=
  tameScalarMultiplier 3
    (mixedRootBlock parameters (assignmentFiber assignment 0).card base (fiberTuple assignment 0 directions))
    (mixedSeedFieldBlock parameters (assignmentFiber assignment 1).card base (fiberTuple assignment 1 directions))

private theorem block_cast {parameters : PhaseParameters} {Value : Type*}
    (family : (order : ℕ) → Input parameters → (Fin order → Input parameters) → Value)
    {count count' : ℕ} (equal : count = count') (base : Input parameters)
    (tuple : Fin count' → Input parameters) :
    family count base (tuple ∘ Fin.cast equal) = family count' base tuple := by
  subst equal
  rfl

theorem mixedRootSeedTerm_snoc_zero (parameters : PhaseParameters) {order : ℕ}
    (assignment : Fin order → Fin 2) (base : Input parameters)
    (directions : Fin (order + 1) → Input parameters) :
    mixedRootSeedTerm parameters (Fin.snoc assignment 0) base directions =
      tameScalarMultiplier 3
        (mixedRootBlock parameters ((assignmentFiber assignment 0).card + 1) base
          (Fin.snoc (fiberTuple assignment 0 (fun position => directions position.castSucc))
            (directions (Fin.last order))))
        (mixedSeedFieldBlock parameters (assignmentFiber assignment 1).card base
          (fiberTuple assignment 1 (fun position => directions position.castSucc))) := by
  unfold mixedRootSeedTerm
  rw [fiberTuple_snoc_self, fiberTuple_snoc_of_ne assignment 0 (by decide : (1 : Fin 2) ≠ 0),
    block_cast (mixedRootBlock parameters), block_cast (mixedSeedFieldBlock parameters)]

theorem mixedRootSeedTerm_snoc_one (parameters : PhaseParameters) {order : ℕ}
    (assignment : Fin order → Fin 2) (base : Input parameters)
    (directions : Fin (order + 1) → Input parameters) :
    mixedRootSeedTerm parameters (Fin.snoc assignment 1) base directions =
      tameScalarMultiplier 3
        (mixedRootBlock parameters (assignmentFiber assignment 0).card base
          (fiberTuple assignment 0 (fun position => directions position.castSucc)))
        (mixedSeedFieldBlock parameters ((assignmentFiber assignment 1).card + 1) base
          (Fin.snoc (fiberTuple assignment 1 (fun position => directions position.castSucc))
            (directions (Fin.last order)))) := by
  unfold mixedRootSeedTerm
  rw [fiberTuple_snoc_of_ne assignment 1 (by decide : (0 : Fin 2) ≠ 1), fiberTuple_snoc_self,
    block_cast (mixedRootBlock parameters), block_cast (mixedSeedFieldBlock parameters)]

theorem mixedRootSeedField_succ (parameters : PhaseParameters) (order : ℕ)
    (base : Input parameters) (directions : Fin (order + 1) → Input parameters) :
    q23MixedRootSeedField parameters (order + 1) base directions =
      ∑ assignment : Fin order → Fin 2,
        (mixedRootSeedTerm parameters (Fin.snoc assignment 0) base directions +
          mixedRootSeedTerm parameters (Fin.snoc assignment 1) base directions) := by
  change (∑ assignment : Fin (order + 1) → Fin 2, mixedRootSeedTerm parameters assignment base directions) = _
  rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ => Fin 2))
    (fun pair => mixedRootSeedTerm parameters (Fin.snoc pair.2 pair.1) base directions)
    (fun extended => mixedRootSeedTerm parameters extended base directions) (fun _ => rfl),
    Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Fin.sum_univ_two]

theorem mixedRootBlock_genuine (parameters : PhaseParameters) (order : ℕ)
    (base : Input parameters) (directions : Fin (order + 1) → Input parameters)
    (axis : ChartAxisCondition base.2.2) :
    HasEnvDerivAt
      (fun t : ℝ => mixedRootBlock parameters order (base + t • directions (Fin.last order))
        (fun position => directions position.castSucc))
      (mixedRootBlock parameters (order + 1) base directions) := by
  have genuine := rootDerivativeFamily_genuine order base.2.2.1
    (fun position => (directions position).2.2.1) axis
  apply genuine.congr_curve
  intro t
  change rootDerivativeFamily order (base.2.2.1 + t • (directions (Fin.last order)).2.2.1) _ = _
  have scalar : t • (directions (Fin.last order)).2.2.1 =
      (t : ℂ) • (directions (Fin.last order)).2.2.1 := by
    exact (Complex.coe_smul t ((directions (Fin.last order)).2.2.1)).symm
  rw [scalar]

end Grad.MixedQuotientComposition
