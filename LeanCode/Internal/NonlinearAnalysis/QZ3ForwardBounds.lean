import QZ2ActualForward

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1600000

open scoped BigOperators ContDiff

namespace Grad.SmoothForward

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.Q24Realization Grad.NonlinearQuotientBounds

theorem stateDirection_oneHigh (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ)
    (base : RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
    (direction : stateRange parameters reference insideR (grade + 6) (realHighLarge grade)) :
    realCompletedOneHigh parameters reference insideR grade 1 base
      (fun _ => stateDirection parameters reference insideR (grade + 6) (realHighLarge grade) direction) =
    (1 + ‖base‖) * ‖stateLowering parameters reference insideR realLowLarge (realLowLeHigh grade) direction‖ +
      ‖direction‖ := by
  have empty : (Finset.univ : Finset (Fin 1)).erase 0 = ∅ := by decide
  simp only [realCompletedOneHigh, Fin.prod_univ_one, Fin.sum_univ_one, empty,
    Finset.prod_empty, mul_one]
  rw [stateDirection_lowering parameters reference insideR realLowLarge (realLowLeHigh grade),
    stateDirection_norm, stateDirection_norm]

/-- Exact one-high bound at a smooth base, uniform on the prescribed low
state ball. Curvature is a fixed finite parameter, absorbed only in the
constant, not inserted into the high state norm. -/
theorem actualSmoothForward_tame (parameters : PhaseParameters) (cellLength epsilon : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 4 ≤ grade) (bound : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : stateSmoothRange parameters reference insideR),
      ChartAxisCondition (smoothingChartCore parameters base.val) →
      ‖stateSmoothEmbedding parameters reference insideR 4 realLowLarge base‖ ≤ bound →
      ∀ direction : stateRange parameters reference insideR (grade + 6) (realHighLarge grade),
      ‖actualSmoothForward parameters cellLength reference insideR seed insideS grade large (epsilon, base) direction‖ ≤
      constant * ((1 + ‖stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade) base‖) *
        ‖stateLowering parameters reference insideR realLowLarge (realLowLeHigh grade) direction‖ + ‖direction‖) := by
  obtain ⟨constant, nonneg, estimate⟩ := completedRealFixedSlice_derivative_bound parameters cellLength
    reference insideR seed insideS grade (forwardLarge large) 1 (|epsilon| + bound)
  refine ⟨constant * (1 + |epsilon|), mul_nonneg nonneg (by positivity), fun base axis bounded direction => ?_⟩
  have inside := (realJointDomain_core_iff parameters reference insideR (grade + 6)
    (realHighLarge grade) (epsilon, base)).2 axis
  have low : ‖realJointLowering parameters reference insideR realLowLarge (realLowLeHigh grade)
      (realJointCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade) (epsilon, base))‖ ≤
      |epsilon| + bound := by
    rw [realJointLowering_core, realJointCoreEmbed_norm]
    exact add_le_add le_rfl bounded
  have result := estimate (realJointCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade) (epsilon, base))
    (fun _ => stateDirection parameters reference insideR (grade + 6) (realHighLarge grade) direction) inside low
  rw [iteratedFDeriv_one_apply, stateDirection_oneHigh, realJointCoreEmbed_norm] at result
  apply result.trans
  change constant * ((1 + (|epsilon| + ‖stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade) base‖)) *
      ‖stateLowering parameters reference insideR realLowLarge (realLowLeHigh grade) direction‖ + ‖direction‖) ≤ _
  have highNonneg := norm_nonneg (stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade) base)
  have lowNonneg := norm_nonneg (stateLowering parameters reference insideR realLowLarge (realLowLeHigh grade) direction)
  have directionNonneg := norm_nonneg direction
  have term := mul_nonneg (mul_nonneg (abs_nonneg epsilon) highNonneg) lowNonneg
  have other := mul_nonneg (abs_nonneg epsilon) directionNonneg
  nlinarith

theorem actualSmoothForward_operator_bound (parameters : PhaseParameters) (cellLength epsilon : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 4 ≤ grade) (bound : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : stateSmoothRange parameters reference insideR),
      ChartAxisCondition (smoothingChartCore parameters base.val) →
      ‖stateSmoothEmbedding parameters reference insideR 4 realLowLarge base‖ ≤ bound →
      ‖actualSmoothForward parameters cellLength reference insideR seed insideS grade large (epsilon, base)‖ ≤
        constant * (2 + ‖stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade) base‖) := by
  obtain ⟨constant, nonneg, estimate⟩ := actualSmoothForward_tame parameters cellLength epsilon reference insideR seed insideS grade large bound
  refine ⟨constant, nonneg, fun base axis bounded => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg nonneg (show 0 ≤ 2 + ‖stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade) base‖ by positivity)) ?_
  intro direction
  have lowering := stateLowering_norm_le parameters reference insideR realLowLarge (realLowLeHigh grade) direction
  have first : (1 + ‖stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade) base‖) *
      ‖stateLowering parameters reference insideR realLowLarge (realLowLeHigh grade) direction‖ ≤
      (1 + ‖stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade) base‖) * ‖direction‖ :=
    mul_le_mul_of_nonneg_left lowering (by positivity)
  calc
    _ ≤ constant * ((1 + ‖stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade) base‖) *
      ‖stateLowering parameters reference insideR realLowLarge (realLowLeHigh grade) direction‖ + ‖direction‖) :=
      estimate base axis bounded direction
    _ ≤ constant * ((1 + ‖stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade) base‖) *
      ‖direction‖ + ‖direction‖) := mul_le_mul_of_nonneg_left (add_le_add first le_rfl) nonneg
    _ = constant * (2 + ‖stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade) base‖) * ‖direction‖ := by ring

end Grad.SmoothForward
