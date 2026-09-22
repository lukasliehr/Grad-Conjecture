import QYP18PhysicalPrimitiveDerivatives

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 600000

open scoped ContDiff

namespace Grad.PhysicalCoordinates

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.QuotientProjection
open Grad.Q24Realization Grad.NonlinearQuotientBounds Grad.SmoothForward

theorem completedRealPhysicalFixedSlice_derivative_inclusion (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (order : ℕ) (base : RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
    (inside : base ∈ realJointDomain parameters reference insideR (grade + 6) (realHighLarge grade))
    (directions : Fin order → RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) :
    sourceInclusion parameters grade large (iteratedFDeriv ℝ order
      (completedRealPhysicalFixedSlice parameters cellLength reference insideR seed grade large) base directions) =
    iteratedFDeriv ℝ order (completedPhysicalFixedSlice parameters cellLength reference insideR seed insideS grade)
      (realJointInclusion parameters reference insideR (grade + 6) (realHighLarge grade) base)
      (fun position => realJointInclusion parameters reference insideR (grade + 6) (realHighLarge grade) (directions position)) := by
  let : NormedSpace ℝ (RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) := inferInstance
  apply derivative_compatibility_on_open
    (realJointInclusion parameters reference insideR (grade + 6) (realHighLarge grade))
    (sourceInclusion parameters grade large)
    (completedRealPhysicalFixedSlice parameters cellLength reference insideR seed grade large)
    (completedPhysicalFixedSlice parameters cellLength reference insideR seed insideS grade)
    (realJointDomain parameters reference insideR (grade + 6) (realHighLarge grade))
    (jointDomain parameters (grade + 6))
    (realJointDomain_isOpen parameters reference insideR (grade + 6) (realHighLarge grade))
    (jointDomain_isOpen parameters (grade + 6)) (fun _ member => member)
    (completedRealPhysicalFixedSlice_contDiffOn parameters cellLength reference insideR seed insideS grade large)
    (completedPhysicalFixedSlice_contDiffOn parameters cellLength reference insideR seed insideS grade)
    _ order base inside directions
  intro state member
  unfold completedRealPhysicalFixedSlice
  rw [completedRealPhysicalMixedSlice_inclusion parameters cellLength reference insideR grade large _
    (realMixedAtSeed_mem parameters reference insideR _ _ seed insideS state member)]
  rfl

/-- The explicit physical first core formula: the actual quotient derivative
at the physical reference state, applied to the actual physical chart derivative. -/
def literalPhysicalSmoothForwardRows (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (direction : stateSmoothRange parameters reference insideR) : QuotientRows parameters :=
  quotientRowsDerivative parameters cellLength 1
    (physicalReferenceState parameters reference insideR seed insideS
      (realJointCoreToJoint parameters reference insideR base))
    (fun _ => physicalFixedReferenceFamily parameters reference insideR seed insideS 1
      (realJointCoreToJoint parameters reference insideR base)
      (fun _ => realJointCoreToJoint parameters reference insideR (0, direction)))

theorem actualPhysicalSmoothForward_core (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 4 ≤ grade) (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (direction : stateSmoothRange parameters reference insideR) :
    sourceInclusion parameters grade (forwardLarge large)
      (actualPhysicalSmoothForward parameters cellLength reference insideR seed grade large base
        (stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade) direction)) =
    quotientEta parameters grade (literalPhysicalSmoothForwardRows parameters cellLength reference insideR seed insideS base direction) := by
  have identity := completedRealPhysicalFixedSlice_derivative_inclusion parameters cellLength reference insideR seed insideS
    grade (forwardLarge large) 1 (realJointCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade) base)
    ((realJointDomain_core_iff parameters reference insideR _ _ base).2 axis)
    (fun _ => realJointCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade) (0, direction))
  rw [iteratedFDeriv_one_apply, iteratedFDeriv_one_apply, realJointInclusion_core, realJointInclusion_core] at identity
  exact identity.trans (completedPhysicalFixedSlice_first_core parameters cellLength reference insideR seed insideS grade
    (realJointCoreToJoint parameters reference insideR base)
    (realJointCoreToJoint parameters reference insideR (0, direction)) axis)

theorem literalPhysicalSmoothForwardRows_mem (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (direction : stateSmoothRange parameters reference insideR) :
    literalPhysicalSmoothForwardRows parameters cellLength reference insideR seed insideS base direction ∈ sourceSmoothRange parameters := by
  apply (quotientEta_mem_iff parameters 4 (by omega) _).1
  rw [← actualPhysicalSmoothForward_core parameters cellLength reference insideR seed insideS 4 (le_refl 4) base axis direction]
  exact (actualPhysicalSmoothForward parameters cellLength reference insideR seed 4 (le_refl 4) base
    (stateSmoothEmbedding parameters reference insideR 10 (realHighLarge 4) direction)).property

end Grad.PhysicalCoordinates
