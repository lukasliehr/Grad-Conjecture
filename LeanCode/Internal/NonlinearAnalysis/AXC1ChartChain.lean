import QX8Consumer
import AxisSplitConsumer

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.ChartAxisSplit

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.AxisSplit Grad.Q24Realization Grad.SmoothForward

variable {parameters : PhaseParameters}

section Chain

variable (family : (order : ℕ) → JointState parameters →
  (Fin order → JointState parameters) → QuotientState parameters)

theorem termArguments_zero {slots : ℕ} (base : JointState parameters)
    (directions : Fin 0 → JointState parameters) :
    termArguments family (default : Fin 0 → Fin slots) base directions =
      fun _ => family 0 base (fun position => position.elim0) := by
  funext slot
  unfold termArguments
  have emptyCard : (assignmentFiber (default : Fin 0 → Fin slots) slot).card = 0 :=
    Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem fun position _ => position.elim0)
  rw [show fiberTuple (default : Fin 0 → Fin slots) slot directions =
      (fun position : Fin 0 => position.elim0) ∘ Fin.cast emptyCard from
        funext fun index => (Fin.cast emptyCard index).elim0, family_cast family]

theorem partComposedDerivative_one {slots : ℕ}
    (part : MultilinearMap ℂ (fun _ : Fin slots => QuotientState parameters) (QuotientRows parameters))
    (base : JointState parameters) (direction : JointState parameters) :
    partComposedDerivative family part 1 base (fun _ => direction) =
      diagonalDerivative part 1 (family 0 base (fun position => position.elim0))
        ![family 1 base (fun _ => direction)] := by
  rw [partComposedDerivative_succ (order := 0), Fintype.sum_unique,
    diagonalDerivative_one]
  apply Finset.sum_congr rfl
  intro slot _
  unfold termValue
  rw [termArguments_snoc, termArguments_zero]
  congr 2

/-- The accepted set-partition tower specializes to the actual first
polynomial derivative applied to the actual first inner derivative. -/
theorem composedDerivative_one (cellLength : ℝ) (base direction : JointState parameters) :
    composedDerivative family cellLength 1 base (fun _ => direction) =
      quotientRowsDerivative parameters cellLength 1
        (family 0 base (fun position => position.elim0))
        ![family 1 base (fun _ => direction)] := by
  simp only [composedDerivative, quotientRowsDerivative, partComposedDerivative_one]

end Chain

theorem fixedSliceDerivative_one (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base direction : JointState parameters) :
    fixedSliceDerivative parameters cellLength reference insideR seed insideS 1 base (fun _ => direction) =
      quotientRowsDerivative parameters cellLength 1
        (referenceState parameters reference insideR seed insideS base)
        ![referenceFamily parameters reference insideR seed insideS 1 base (fun _ => direction)] := by
  unfold fixedSliceDerivative
  rw [composedDerivative_one, referenceFamily_zeroth]

end Grad.ChartAxisSplit
