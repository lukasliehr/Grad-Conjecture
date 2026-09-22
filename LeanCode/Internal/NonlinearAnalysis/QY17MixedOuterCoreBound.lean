import QY16MixedOuterIdentification

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

open scoped BigOperators ContDiff

namespace Grad.MixedQuotientComposition

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.Q24Realization

variable {parameters : PhaseParameters}

theorem inputOneHigh_reindex (high low : ℕ) (base : Input parameters) {order : ℕ}
    (directions : Fin order → Input parameters) (permutation : Equiv.Perm (Fin order)) :
    inputOneHigh high low base (fun position => directions (permutation position)) =
      inputOneHigh high low base directions := by
  unfold inputOneHigh
  rw [Equiv.prod_comp permutation (fun position => directionNorm low (directions position)),
    oneHigh_sum_reindex permutation (fun position => directionNorm high (directions position))
      (fun position => directionNorm low (directions position))]

/-- The actual completed mixed core derivative inherits the literal outer
one-high estimate. Both analytic premises concern the genuine inner tower;
the final Q23 assembly supplies them. -/
theorem mixedComposedDerivative_core_bound
    (family : (order : ℕ) → Input parameters →
      (Fin order → Input parameters) → QuotientState parameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (zeroth : ∀ (base : Input parameters) (insideS : base.1 ∈ Seed.parameterDomain),
      ChartAxisCondition base.2.2 → ∀ directions,
        family 0 base directions = referenceState parameters reference insideR base.1 insideS base.2)
    (genuine : ∀ order base (directions : Fin (order + 1) → Input parameters),
      CoreAdmissible base → IsStateDirectionalDerivative
        (fun point => family order point (fun position => directions position.castSucc))
        base (directions (Fin.last order)) (family (order + 1) base directions))
    (Admissible : Input parameters → Prop)
    (coreAdmissible : ∀ base, Admissible base → CoreAdmissible base)
    (innerBound : ∀ (grade count : ℕ), ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : Input parameters) (tuple : Fin count → Input parameters),
        Admissible base →
        stateNorm grade (family count base tuple) ≤ constant * inputOneHigh grade 4 base tuple)
    (cellLength : ℝ) (grade order : ℕ) (ball : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : Input parameters) (directions : Fin order → Input parameters),
        Admissible base → baseNorm 4 base ≤ ball →
        ‖iteratedFDeriv ℝ order (completedMixedSlice parameters cellLength reference grade)
          (mixedCoreEmbed parameters (grade + 6) base)
          (fun position => mixedCoreEmbed parameters (grade + 6) (directions position))‖ ≤
          constant * mixedCompletedOneHigh parameters grade order
            (mixedCoreEmbed parameters (grade + 6) base)
            (fun position => mixedCoreEmbed parameters (grade + 6) (directions position)) := by
  obtain ⟨constant, nonneg, estimate⟩ :=
    composedDerivative_bound family Admissible innerBound cellLength grade order ball
  refine ⟨2 * constant, by positivity, fun base directions admissible bounded => ?_⟩
  rw [mixedComposedDerivative_core family reference insideR zeroth genuine cellLength grade order
    base (coreAdmissible base admissible)]
  calc
    _ ≤ 2 * rowsGradeNorm grade
        (composedDerivative family cellLength order base (fun position => directions position.rev)) :=
      quotientEta_norm_le_rows parameters grade _
    _ ≤ 2 * (constant * inputOneHigh (grade + 6) 4 base (fun position => directions position.rev)) :=
      mul_le_mul_of_nonneg_left
        (estimate base (fun position => directions position.rev) admissible bounded) (by norm_num)
    _ = _ := by
      have reindex := inputOneHigh_reindex (grade + 6) 4 base directions Fin.revPerm
      change inputOneHigh (grade + 6) 4 base (fun position => directions position.rev) = _ at reindex
      rw [reindex, inputOneHigh_completed]
      ring

end Grad.MixedQuotientComposition
