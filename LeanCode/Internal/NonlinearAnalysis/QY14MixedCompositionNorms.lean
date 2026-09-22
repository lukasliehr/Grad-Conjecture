import QY13MixedCompositionGenuine

noncomputable section

open scoped BigOperators

namespace Grad.MixedQuotientComposition

open Grad.CartesianState Grad.NonlinearQuotientBounds

variable {parameters : PhaseParameters}

/-- Literal seed-coordinate sum, curvature norm and original chart norm. -/
def directionNorm (grade : ℕ) (direction : Input parameters) : ℝ :=
  (∑ coordinate, |direction.1 coordinate|) + jointNorm grade direction.2

/-- Only the infinite-dimensional state occurs in the high base factor. -/
def baseNorm (grade : ℕ) (base : Input parameters) : ℝ := chartStateNorm grade base.2.2

theorem directionNorm_nonneg (grade : ℕ) (direction : Input parameters) : 0 ≤ directionNorm grade direction :=
  add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (jointNorm_nonneg grade direction.2)

theorem baseNorm_nonneg (grade : ℕ) (base : Input parameters) : 0 ≤ baseNorm grade base :=
  chartStateNorm_nonneg grade base.2.2

def inputOneHigh (high low : ℕ) (base : Input parameters) {order : ℕ}
    (directions : Fin order → Input parameters) : ℝ :=
  (1 + baseNorm high base) * ∏ position, directionNorm low (directions position) +
    ∑ position, directionNorm high (directions position) *
      ∏ other ∈ Finset.univ.erase position, directionNorm low (directions other)

theorem inputOneHigh_nonneg (high low : ℕ) (base : Input parameters) {order : ℕ}
    (directions : Fin order → Input parameters) : 0 ≤ inputOneHigh high low base directions :=
  add_nonneg
    (mul_nonneg (by linarith [baseNorm_nonneg high base])
      (Finset.prod_nonneg fun _ _ => directionNorm_nonneg low _))
    (Finset.sum_nonneg fun _ _ => mul_nonneg (directionNorm_nonneg high _)
      (Finset.prod_nonneg fun _ _ => directionNorm_nonneg low _))

theorem inputOneHigh_completed (grade order : ℕ) (base : Input parameters)
    (directions : Fin order → Input parameters) :
    inputOneHigh (grade + 6) 4 base directions =
      Grad.Q24Realization.mixedCompletedOneHigh parameters grade order
        (Grad.Q24Realization.mixedCoreEmbed parameters (grade + 6) base)
        (fun position => Grad.Q24Realization.mixedCoreEmbed parameters (grade + 6) (directions position)) := by
  rw [Grad.Q24Realization.mixedCompletedOneHigh_core]
  rfl

end Grad.MixedQuotientComposition
