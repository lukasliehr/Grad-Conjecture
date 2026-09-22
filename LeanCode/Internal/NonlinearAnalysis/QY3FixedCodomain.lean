import QY2ExactRestriction

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

open scoped ContDiff

namespace Grad.Q24Realization

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.RealFixedRanges Grad.SmoothingFamily Grad.AxisCore Grad.QuotientProjection

theorem sourceRetraction_fixes (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade)
    (value : sourceRange parameters grade large) :
    sourceRetraction parameters grade large value = value :=
  realRetraction_fixes _ _ _ _ _ value

/-- Actual Q24 with its canonical real compatible target. The defining
expression is a dependent codomain restriction of the literal ambient map,
not a target projection. -/
def completedRealFixedSlice (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade) →
      sourceRange parameters grade large :=
  exactRangeRestriction
    (completedRealFixedSliceAmbient parameters cellLength reference insideR seed insideS grade)
    (realJointDomain parameters reference insideR (grade + 6) (realHighLarge grade))
    (sourceRange parameters grade large)
    (completedRealFixedSliceAmbient_mem parameters cellLength reference insideR seed insideS grade large)

theorem completedRealFixedSlice_inclusion (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (state : RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
    (inside : state ∈ realJointDomain parameters reference insideR (grade + 6) (realHighLarge grade)) :
    sourceInclusion parameters grade large
      (completedRealFixedSlice parameters cellLength reference insideR seed insideS grade large state) =
      completedRealFixedSliceAmbient parameters cellLength reference insideR seed insideS grade state :=
  exactRangeRestriction_coe _ _ _ _ state inside

theorem completedRealFixedSlice_contDiffOn (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    ContDiffOn ℝ ∞ (completedRealFixedSlice parameters cellLength reference insideR seed insideS grade large)
      (realJointDomain parameters reference insideR (grade + 6) (realHighLarge grade)) :=
  exactRangeRestriction_contDiffOn _ _ _ _ (sourceRetraction parameters grade large)
    (sourceRetraction_fixes parameters grade large)
    (completedRealFixedSliceAmbient_contDiffOn parameters cellLength reference insideR seed insideS grade)

theorem completedRealFixedSlice_core (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (state : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters state.2.val)) :
    sourceInclusion parameters grade large
      (completedRealFixedSlice parameters cellLength reference insideR seed insideS grade large
        (realJointCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade) state)) =
      quotientEta parameters grade (fixedSliceMap parameters cellLength reference insideR seed insideS
        (realJointCoreToJoint parameters reference insideR state)) := by
  rw [completedRealFixedSlice_inclusion parameters cellLength reference insideR seed insideS grade large _
    ((realJointDomain_core_iff parameters reference insideR (grade + 6) (realHighLarge grade) state).2 axis)]
  exact completedRealFixedSliceAmbient_core parameters cellLength reference insideR seed insideS grade state axis

theorem completedRealFixedSlice_derivative_inclusion (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (order : ℕ) (state : RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
    (inside : state ∈ realJointDomain parameters reference insideR (grade + 6) (realHighLarge grade))
    (directions : Fin order → RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) :
    sourceInclusion parameters grade large (iteratedFDeriv ℝ order
      (completedRealFixedSlice parameters cellLength reference insideR seed insideS grade large) state directions) =
      iteratedFDeriv ℝ order
        (completedRealFixedSliceAmbient parameters cellLength reference insideR seed insideS grade) state directions :=
  exactRangeRestriction_derivative_coe _ _ _ _ (sourceRetraction parameters grade large)
    (sourceRetraction_fixes parameters grade large)
    (realJointDomain_isOpen parameters reference insideR (grade + 6) (realHighLarge grade))
    (completedRealFixedSliceAmbient_contDiffOn parameters cellLength reference insideR seed insideS grade)
    order state inside directions

end Grad.Q24Realization
