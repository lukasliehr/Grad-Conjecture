import QYP19PhysicalForwardCore

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 600000

open scoped BigOperators ContDiff

namespace Grad.PhysicalCoordinates

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.Q24Realization Grad.NonlinearQuotientBounds Grad.SmoothForward

theorem completedPhysicalFixedSlice_derivative_bound (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade order : ℕ) (bound : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : JointAmbient parameters (grade + 6))
        (directions : Fin order → JointAmbient parameters (grade + 6)),
        base ∈ jointDomain parameters (grade + 6) →
        ‖jointLowering parameters (show 4 ≤ grade + 6 by omega) base‖ ≤ bound →
        ‖iteratedFDeriv ℝ order
          (completedPhysicalFixedSlice parameters cellLength reference insideR seed insideS grade) base directions‖ ≤
          constant * completedOneHigh parameters grade order base directions := by
  obtain ⟨constant, nonneg, bounded⟩ := completedPhysicalFixedSlice_derivative_core_bound parameters cellLength
    reference insideR seed insideS grade order (bound + 1)
  refine ⟨constant, nonneg, fun base directions inside lowBound => ?_⟩
  apply derivative_bound_of_dense_core
    (jointCoreEmbed parameters (grade + 6)) (jointCoreEmbed_denseRange parameters (grade + 6))
    (completedPhysicalFixedSlice parameters cellLength reference insideR seed insideS grade)
    (jointDomain parameters (grade + 6))
    (jointDomain_isOpen parameters (grade + 6))
    (completedPhysicalFixedSlice_contDiffOn parameters cellLength reference insideR seed insideS grade)
    order (fun state => ‖jointLowering parameters (show 4 ≤ grade + 6 by omega) state‖)
    (jointLowering parameters (show 4 ≤ grade + 6 by omega)).continuous.norm (bound + 1)
    (fun pair => constant * completedOneHigh parameters grade order pair.1 pair.2)
    (continuous_const.mul (completedOneHigh_continuous parameters grade order))
  · intro core tuple coreInside strict
    rw [completedOneHigh_core]
    rw [jointLowering_core, jointCoreEmbed_norm] at strict
    exact bounded core tuple ((jointDomain_core_iff parameters (grade + 6) core).1 coreInside) strict.le
  · exact inside
  · exact lowBound.trans_lt (lt_add_one bound)


theorem completedRealPhysicalFixedSlice_derivative_bound (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (order : ℕ) (bound : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
        (directions : Fin order → RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade)),
        base ∈ realJointDomain parameters reference insideR (grade + 6) (realHighLarge grade) →
        ‖realJointLowering parameters reference insideR realLowLarge (realLowLeHigh grade) base‖ ≤ bound →
        ‖iteratedFDeriv ℝ order
          (completedRealPhysicalFixedSlice parameters cellLength reference insideR seed grade large) base directions‖ ≤
          constant * realCompletedOneHigh parameters reference insideR grade order base directions := by
  obtain ⟨constant, nonneg, estimate⟩ := completedPhysicalFixedSlice_derivative_bound parameters cellLength
    reference insideR seed insideS grade order bound
  refine ⟨constant, nonneg, fun base directions inside bounded => ?_⟩
  rw [← sourceInclusion_norm parameters grade large,
    completedRealPhysicalFixedSlice_derivative_inclusion parameters cellLength reference insideR seed insideS
      grade large order base inside, ← realCompletedOneHigh_inclusion]
  apply estimate _ _ inside
  rw [← realJointLowering_inclusion parameters reference insideR realLowLarge,
    realJointInclusion_norm]
  exact bounded

theorem actualPhysicalSmoothForward_tame (parameters : PhaseParameters) (cellLength epsilon : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 4 ≤ grade) (bound : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : stateSmoothRange parameters reference insideR),
      ChartAxisCondition (smoothingChartCore parameters base.val) →
      ‖stateSmoothEmbedding parameters reference insideR 4 realLowLarge base‖ ≤ bound →
      ∀ direction : stateRange parameters reference insideR (grade + 6) (realHighLarge grade),
      ‖actualPhysicalSmoothForward parameters cellLength reference insideR seed grade large (epsilon, base) direction‖ ≤
      constant * ((1 + ‖stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade) base‖) *
        ‖stateLowering parameters reference insideR realLowLarge (realLowLeHigh grade) direction‖ + ‖direction‖) := by
  obtain ⟨constant, nonneg, estimate⟩ := completedRealPhysicalFixedSlice_derivative_bound parameters cellLength
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

theorem actualPhysicalSmoothForward_operator_bound (parameters : PhaseParameters) (cellLength epsilon : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 4 ≤ grade) (bound : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : stateSmoothRange parameters reference insideR),
      ChartAxisCondition (smoothingChartCore parameters base.val) →
      ‖stateSmoothEmbedding parameters reference insideR 4 realLowLarge base‖ ≤ bound →
      ‖actualPhysicalSmoothForward parameters cellLength reference insideR seed grade large (epsilon, base)‖ ≤
        constant * (2 + ‖stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade) base‖) := by
  obtain ⟨constant, nonneg, estimate⟩ := actualPhysicalSmoothForward_tame parameters cellLength epsilon reference insideR seed insideS grade large bound
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

end Grad.PhysicalCoordinates

