import Q24RealDomain
import Q24ClosedRange

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1200000

open scoped BigOperators ContDiff

namespace Grad.Q24Realization

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisCore Grad.SmoothingFamily Grad.RealFixedRanges Grad.ConstrainedGrades

def realJointLowering {lower upper : ℕ} (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (large : 3 ≤ lower) (ordered : lower ≤ upper) :
    RealJointAmbient parameters reference insideR upper (large.trans ordered) →L[ℝ]
      RealJointAmbient parameters reference insideR lower large :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ ℝ
    (stateRange parameters reference insideR lower large)).symm.toContinuousLinearMap.comp
      (((ContinuousLinearMap.id ℝ ℝ).prodMap
        (stateLowering parameters reference insideR large ordered)).comp
        (WithLp.prodContinuousLinearEquiv 1 ℝ ℝ
          (stateRange parameters reference insideR upper (large.trans ordered))).toContinuousLinearMap)

theorem realJointLowering_inclusion {lower upper : ℕ} (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (state : RealJointAmbient parameters reference insideR upper (large.trans ordered)) :
    realJointInclusion parameters reference insideR lower large
      (realJointLowering parameters reference insideR large ordered state) =
    jointLowering parameters ordered
      (realJointInclusion parameters reference insideR upper (large.trans ordered) state) := rfl

theorem completedRealFixedSliceAmbient_derivative (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade order : ℕ)
    (base : RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
    (inside : base ∈ realJointDomain parameters reference insideR (grade + 6) (realHighLarge grade))
    (directions : Fin order → RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) :
    iteratedFDeriv ℝ order
      (completedRealFixedSliceAmbient parameters cellLength reference insideR seed insideS grade) base directions =
    iteratedFDeriv ℝ order
      (completedFixedSlice parameters cellLength reference insideR seed insideS grade)
      (realJointInclusion parameters reference insideR (grade + 6) (realHighLarge grade) base)
      (fun position => realJointInclusion parameters reference insideR (grade + 6) (realHighLarge grade) (directions position)) := by
  let : NormedSpace ℝ (RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) := inferInstance
  exact iteratedFDeriv_precomp_on_open
    (realJointInclusion parameters reference insideR (grade + 6) (realHighLarge grade))
    (completedFixedSlice parameters cellLength reference insideR seed insideS grade)
    (jointDomain parameters (grade + 6)) (jointDomain_isOpen parameters (grade + 6))
    (completedFixedSlice_contDiffOn parameters cellLength reference insideR seed insideS grade)
    order base inside directions

/-- The exact one-high sum on the completed real reference slice. -/
def realCompletedOneHigh (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade order : ℕ)
    (base : RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
    (directions : Fin order → RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) : ℝ :=
  (1 + ‖base‖) * ∏ position,
      ‖realJointLowering parameters reference insideR realLowLarge (realLowLeHigh grade) (directions position)‖ +
    ∑ position, ‖directions position‖ *
      ∏ other ∈ Finset.univ.erase position,
        ‖realJointLowering parameters reference insideR realLowLarge (realLowLeHigh grade) (directions other)‖

theorem realCompletedOneHigh_inclusion (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade order : ℕ)
    (base : RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
    (directions : Fin order → RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) :
    completedOneHigh parameters grade order
      (realJointInclusion parameters reference insideR (grade + 6) (realHighLarge grade) base)
      (fun position => realJointInclusion parameters reference insideR (grade + 6) (realHighLarge grade) (directions position)) =
    realCompletedOneHigh parameters reference insideR grade order base directions := by
  simp only [completedOneHigh, realCompletedOneHigh,
    ← realJointLowering_inclusion parameters reference insideR realLowLarge (realLowLeHigh grade),
    realJointInclusion_norm]

/-- Fixed-seed Q22 survives restriction with its exact sum norms and loss
six, with no restriction on the high norm of the state. -/
theorem completedRealFixedSliceAmbient_derivative_bound (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade order : ℕ) (bound : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
        (directions : Fin order → RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade)),
        base ∈ realJointDomain parameters reference insideR (grade + 6) (realHighLarge grade) →
        ‖realJointLowering parameters reference insideR realLowLarge (realLowLeHigh grade) base‖ ≤ bound →
        ‖iteratedFDeriv ℝ order
          (completedRealFixedSliceAmbient parameters cellLength reference insideR seed insideS grade) base directions‖ ≤
          constant * realCompletedOneHigh parameters reference insideR grade order base directions := by
  let : NormedSpace ℝ (RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) := inferInstance
  obtain ⟨constant, nonneg, estimate⟩ := completedFixedSlice_derivative_bound parameters cellLength
    reference insideR seed insideS grade order bound
  refine ⟨constant, nonneg, fun base directions inside bounded => ?_⟩
  rw [completedRealFixedSliceAmbient_derivative parameters cellLength reference insideR seed insideS
    grade order base inside directions, ← realCompletedOneHigh_inclusion]
  apply estimate _ _ inside
  rw [← realJointLowering_inclusion parameters reference insideR realLowLarge,
    realJointInclusion_norm]
  exact bounded

end Grad.Q24Realization
