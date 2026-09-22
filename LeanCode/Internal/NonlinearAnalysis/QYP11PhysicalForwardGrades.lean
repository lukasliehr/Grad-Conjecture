import QYP10PhysicalForwardBounds

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 600000

open scoped ContDiff

namespace Grad.PhysicalCoordinates

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.Q24Realization Grad.NonlinearQuotientBounds Grad.SmoothForward

theorem completedRealPhysicalFixedSlice_gradeCompatibility {lower upper : ℕ}
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (state : RealJointAmbient parameters reference insideR (upper + 6) (realHighLarge upper))
    (inside : state ∈ realJointDomain parameters reference insideR (upper + 6) (realHighLarge upper)) :
    sourceLowering parameters large ordered
      (completedRealPhysicalFixedSlice parameters cellLength reference insideR seed upper (large.trans ordered) state) =
    completedRealPhysicalFixedSlice parameters cellLength reference insideR seed lower large
      (realJointLowering parameters reference insideR (realHighLarge lower) (Nat.add_le_add_right ordered 6) state) :=
  completedRealPhysicalMixedSlice_gradeCompatibility parameters cellLength reference insideR large ordered
    (realMixedAtSeed parameters reference insideR _ _ seed state)
    (realMixedAtSeed_mem parameters reference insideR _ _ seed insideS state inside)

theorem actualPhysicalSmoothForward_gradeCompatibility {lower upper : ℕ}
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (large : 4 ≤ lower) (ordered : lower ≤ upper)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val)) :
    (sourceLowering parameters (forwardLarge large) ordered).comp
      (actualPhysicalSmoothForward parameters cellLength reference insideR seed upper (large.trans ordered) base) =
    (actualPhysicalSmoothForward parameters cellLength reference insideR seed lower large base).comp
      (stateLowering parameters reference insideR (realHighLarge lower) (Nat.add_le_add_right ordered 6)) := by
  let : NormedSpace ℝ (RealJointAmbient parameters reference insideR (upper + 6) (realHighLarge upper)) := inferInstance
  let : NormedSpace ℝ (RealJointAmbient parameters reference insideR (lower + 6) (realHighLarge lower)) := inferInstance
  apply ContinuousLinearMap.ext
  intro direction
  have identity := derivative_compatibility_on_open
    (realJointLowering parameters reference insideR (realHighLarge lower) (Nat.add_le_add_right ordered 6))
    (sourceLowering parameters (forwardLarge large) ordered)
    (completedRealPhysicalFixedSlice parameters cellLength reference insideR seed upper (forwardLarge (large.trans ordered)))
    (completedRealPhysicalFixedSlice parameters cellLength reference insideR seed lower (forwardLarge large))
    (realJointDomain parameters reference insideR (upper + 6) (realHighLarge upper))
    (realJointDomain parameters reference insideR (lower + 6) (realHighLarge lower))
    (realJointDomain_isOpen parameters reference insideR (upper + 6) (realHighLarge upper))
    (realJointDomain_isOpen parameters reference insideR (lower + 6) (realHighLarge lower))
    (fun value member => (realJointLowering_domain_iff parameters reference insideR
      (realHighLarge lower) (Nat.add_le_add_right ordered 6) value).2 member)
    (completedRealPhysicalFixedSlice_contDiffOn parameters cellLength reference insideR seed insideS upper (forwardLarge (large.trans ordered)))
    (completedRealPhysicalFixedSlice_contDiffOn parameters cellLength reference insideR seed insideS lower (forwardLarge large))
    (completedRealPhysicalFixedSlice_gradeCompatibility parameters cellLength reference insideR seed insideS (forwardLarge large) ordered)
    1 (realJointCoreEmbed parameters reference insideR (upper + 6) (realHighLarge upper) base)
    ((realJointDomain_core_iff parameters reference insideR (upper + 6) (realHighLarge upper) base).2 axis)
    (fun _ => stateDirection parameters reference insideR (upper + 6) (realHighLarge upper) direction)
  rw [iteratedFDeriv_one_apply, iteratedFDeriv_one_apply, realJointLowering_core] at identity
  simp only [stateDirection_lowering] at identity
  exact identity

end Grad.PhysicalCoordinates
