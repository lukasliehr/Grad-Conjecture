import QY14MixedCompositionNorms
import RootUnitTower

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.MixedQuotientComposition

open Grad.CartesianState Grad.NonlinearQuotientBounds

variable {parameters : PhaseParameters}

theorem chartNorm_le_directionNorm (grade : ℕ) (direction : Input parameters) :
    chartStateNorm grade direction.2.2 ≤ directionNorm grade direction := by
  exact (chartStateNorm_snd_le_jointNorm grade direction.2).trans
    (le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => abs_nonneg _))

theorem seedNorm_le_directionNorm (grade : ℕ) (direction : Input parameters) :
    ‖direction.1‖ ≤ directionNorm grade direction := by
  have seed : ‖direction.1‖ ≤ ∑ coordinate, |direction.1 coordinate| := by
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)).2
    intro coordinate
    simpa only [Real.norm_eq_abs] using
      (Finset.single_le_sum (fun index _ => abs_nonneg (direction.1 index))
        (Finset.mem_univ coordinate))
  exact seed.trans (le_add_of_nonneg_right (jointNorm_nonneg grade direction.2))

theorem chartOneHigh_le_inputOneHigh (high low : ℕ) (base : Input parameters) {order : ℕ}
    (directions : Fin order → Input parameters) :
    (1 + chartStateNorm high base.2.2) *
        ∏ position, chartStateNorm low (directions position).2.2 +
      ∑ position, chartStateNorm high (directions position).2.2 *
        ∏ other ∈ Finset.univ.erase position, chartStateNorm low (directions other).2.2 ≤
      inputOneHigh high low base directions := by
  unfold inputOneHigh baseNorm
  have products (indices : Finset (Fin order)) :
      (∏ position ∈ indices, chartStateNorm low (directions position).2.2) ≤
        ∏ position ∈ indices, directionNorm low (directions position) :=
    Finset.prod_le_prod (fun _ _ => chartStateNorm_nonneg _ _)
      (fun position _ => chartNorm_le_directionNorm low (directions position))
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (products Finset.univ)
      (by linarith [chartStateNorm_nonneg high base.2.2])
  · exact Finset.sum_le_sum fun position _ =>
      mul_le_mul (chartNorm_le_directionNorm high (directions position))
        (products (Finset.univ.erase position))
        (Finset.prod_nonneg fun _ _ => chartStateNorm_nonneg _ _)
        (directionNorm_nonneg high (directions position))

/-- The actual root-axis derivative family obeys the original same-grade
one-high bound for mixed inputs. Seed and curvature do not enter the high
base factor, and no norm or analytic width is changed. -/
theorem mixedRootDerivative_bound (grade order : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : Input parameters) (directions : Fin order → Input parameters),
        ChartAxisCondition base.2.2 →
        coefficientEnvelope grade
          (rootDerivativeFamily order base.2.2.1 (fun position => (directions position).2.2.1)) ≤
          constant * inputOneHigh grade 4 base directions := by
  obtain ⟨constant, nonneg, bound⟩ :=
    chartTower_range_envelope_le (parameters := parameters) grade order
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  let factor := (1 + Real.sqrt 2 ^ grade * axisConstant) * (1 + axisConstant) ^ order
  have factorNonneg : 0 ≤ factor := by
    dsimp [factor]
    have axis := axisConstant_pos.le
    positivity
  refine ⟨constant * factor, mul_nonneg nonneg factorNonneg, fun base directions axis => ?_⟩
  have rootBound := bound base.2.2.1
    (chartTangentDirections (fun position => (directions position).2.2))
    (chartAxis_planar_le_half axis)
  have stateBound := towerRange_le_bracket grade base.2.2
    (fun position => (directions position).2.2)
  have combined := stateBound.trans
    (mul_le_mul_of_nonneg_left (chartOneHigh_le_inputOneHigh grade 4 base directions) factorNonneg)
  have result := rootBound.trans (mul_le_mul_of_nonneg_left combined nonneg)
  exact result.trans_eq (by
    change constant * (factor * inputOneHigh grade 4 base directions) = _
    ring)

end Grad.MixedQuotientComposition
