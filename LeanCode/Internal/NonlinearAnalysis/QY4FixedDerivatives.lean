import QY3FixedCodomain

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

open scoped ContDiff

namespace Grad.Q24Realization

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.RealFixedRanges Grad.SmoothingFamily Grad.AxisCore Grad.QuotientProjection

theorem completedRealFixedSlice_derivative_norm (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (order : ℕ) (state : RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
    (inside : state ∈ realJointDomain parameters reference insideR (grade + 6) (realHighLarge grade))
    (directions : Fin order → RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) :
    ‖iteratedFDeriv ℝ order
      (completedRealFixedSlice parameters cellLength reference insideR seed insideS grade large) state directions‖ =
      ‖iteratedFDeriv ℝ order
        (completedRealFixedSliceAmbient parameters cellLength reference insideR seed insideS grade) state directions‖ := by
  rw [← sourceInclusion_norm parameters grade large,
    completedRealFixedSlice_derivative_inclusion parameters cellLength reference insideR seed insideS grade large
      order state inside directions]

theorem completedRealFixedSlice_derivative_bound (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (order : ℕ) (bound : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (state : RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
        (directions : Fin order → RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade)),
        state ∈ realJointDomain parameters reference insideR (grade + 6) (realHighLarge grade) →
        ‖realJointLowering parameters reference insideR realLowLarge (realLowLeHigh grade) state‖ ≤ bound →
        ‖iteratedFDeriv ℝ order
          (completedRealFixedSlice parameters cellLength reference insideR seed insideS grade large) state directions‖ ≤
          constant * realCompletedOneHigh parameters reference insideR grade order state directions := by
  obtain ⟨constant, nonneg, estimate⟩ := completedRealFixedSliceAmbient_derivative_bound parameters cellLength
    reference insideR seed insideS grade order bound
  refine ⟨constant, nonneg, fun state directions inside bounded => ?_⟩
  rw [completedRealFixedSlice_derivative_norm parameters cellLength reference insideR seed insideS grade large
    order state inside directions]
  exact estimate state directions inside bounded

/-- Every actual Fréchet derivative on real constrained core states is
the accepted literal smooth-core derivative, with its original slot order. -/
theorem completedRealFixedSlice_derivative_core (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (order : ℕ) (state : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters state.2.val))
    (directions : Fin order → RealJointCore parameters reference insideR) :
    sourceInclusion parameters grade large (iteratedFDeriv ℝ order
      (completedRealFixedSlice parameters cellLength reference insideR seed insideS grade large)
      (realJointCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade) state)
      (fun position => realJointCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade)
        (directions position))) =
      quotientEta parameters grade (fixedSliceDerivative parameters cellLength reference insideR seed insideS order
        (realJointCoreToJoint parameters reference insideR state)
        (fun position => realJointCoreToJoint parameters reference insideR (directions position.rev))) := by
  have inside := (realJointDomain_core_iff parameters reference insideR (grade + 6)
    (realHighLarge grade) state).2 axis
  rw [completedRealFixedSlice_derivative_inclusion parameters cellLength reference insideR seed insideS
    grade large order _ inside,
    completedRealFixedSliceAmbient_derivative parameters cellLength reference insideR seed insideS
      grade order _ inside]
  simp only [realJointInclusion_core]
  exact completedFixedSlice_derivative_core parameters cellLength reference insideR seed insideS grade order
    (realJointCoreToJoint parameters reference insideR state) axis
    (fun position => realJointCoreToJoint parameters reference insideR (directions position))

/-- Differentiated O21 on the literal smooth core, now derived from the
proved exact real codomain realization rather than assumed as an input. -/
theorem fixedSliceDerivative_constrained_mem (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (order : ℕ) (state : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters state.2.val))
    (directions : Fin order → RealJointCore parameters reference insideR) :
    fixedSliceDerivative parameters cellLength reference insideR seed insideS order
      (realJointCoreToJoint parameters reference insideR state)
      (fun position => realJointCoreToJoint parameters reference insideR (directions position.rev)) ∈
      sourceSmoothRange parameters := by
  apply (quotientEta_mem_iff parameters 3 (le_refl 3) _).1
  rw [← completedRealFixedSlice_derivative_core parameters cellLength reference insideR seed insideS
    3 (le_refl 3) order state axis directions]
  exact (iteratedFDeriv ℝ order
    (completedRealFixedSlice parameters cellLength reference insideR seed insideS 3 (le_refl 3))
    (realJointCoreEmbed parameters reference insideR 9 (realHighLarge 3) state)
    (fun position => realJointCoreEmbed parameters reference insideR 9 (realHighLarge 3)
      (directions position))).property

end Grad.Q24Realization
