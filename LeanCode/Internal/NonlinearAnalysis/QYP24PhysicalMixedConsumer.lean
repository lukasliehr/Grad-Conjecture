import QYP23PhysicalMixedCompletion
import QYP21PhysicalForwardConsumer

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 600000

open scoped ContDiff

namespace Grad.PhysicalCoordinates

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.RealFixedRanges Grad.ConstrainedGrades Grad.QuotientProjection
open Grad.Q24Realization Grad.MixedQuotientComposition

/-- Every mixed seed/curvature/state derivative of the actual real map is
the literal physical core tower, with no target projection in the formula. -/
theorem completedRealPhysicalMixedSlice_derivative_core
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 3 ≤ grade) (order : ℕ)
    (base : RealMixedCore parameters reference insideR) (insideS : base.1 ∈ Seed.parameterDomain)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.2.val))
    (directions : Fin order → RealMixedCore parameters reference insideR) :
    sourceInclusion parameters grade large (iteratedFDeriv ℝ order
      (completedRealPhysicalMixedSlice parameters cellLength reference insideR grade large)
      (realMixedCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade) base)
      (fun position => realMixedCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade)
        (directions position))) =
      quotientEta parameters grade (physicalMixedSliceCoreTower parameters cellLength reference insideR order
        (base.1, realJointCoreToJoint parameters reference insideR base.2)
        (fun position => ((directions position.rev).1,
          realJointCoreToJoint parameters reference insideR (directions position.rev).2))) := by
  exact physicalMixedComposedDerivative_real_core
    (physicalMixedInnerFamily parameters reference insideR) reference insideR
    (fun point inside _ tuple => physicalMixedInnerFamily_zero parameters reference insideR point inside tuple)
    (physicalMixedInnerFamily_genuine parameters reference insideR)
    cellLength grade large order base insideS axis directions

/-- All literal mixed derivatives preserve the actual smooth projection
and reality constraints, obtained from the identical real completed map. -/
theorem physicalMixedSliceCoreTower_constrained_mem
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (order : ℕ) (base : RealMixedCore parameters reference insideR)
    (insideS : base.1 ∈ Seed.parameterDomain)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.2.val))
    (directions : Fin order → RealMixedCore parameters reference insideR) :
    physicalMixedSliceCoreTower parameters cellLength reference insideR order
      (base.1, realJointCoreToJoint parameters reference insideR base.2)
      (fun position => ((directions position).1,
        realJointCoreToJoint parameters reference insideR (directions position).2)) ∈
      sourceSmoothRange parameters := by
  exact physicalMixedComposedDerivative_constrained_mem
    (physicalMixedInnerFamily parameters reference insideR) reference insideR
    (fun point inside _ tuple => physicalMixedInnerFamily_zero parameters reference insideR point inside tuple)
    (physicalMixedInnerFamily_genuine parameters reference insideR)
    cellLength order base insideS axis directions

/-- Universal public Q24 consumer of the coordinate-correct nonlinear map
and its actual fixed-state forward operator, not hypothetical replacement
maps. All parameters and all admissible grades remain quantified. -/
def PhysicalNonlinearTameGoal : Prop :=
  (∀ (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain),
    PhysicalMixedBanachRealization parameters cellLength reference insideR) ∧
  PhysicalSmoothForwardGoal

theorem actualPhysicalNonlinearTame : PhysicalNonlinearTameGoal :=
  ⟨physicalMixedBanachRealization, literalPhysicalSmoothForward_completedCLM⟩

end Grad.PhysicalCoordinates
