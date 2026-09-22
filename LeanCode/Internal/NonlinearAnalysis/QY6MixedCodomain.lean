import QY5FixedGrades
import Q24RealMixed

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

open scoped ContDiff

namespace Grad.Q24Realization

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.RealFixedRanges Grad.SmoothingFamily Grad.AxisCore Grad.QuotientProjection

theorem completedRealMixedSliceAmbient_core_mem (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (state : RealMixedCore parameters reference insideR)
    (inside : realMixedCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade) state ∈
      realMixedDomain parameters reference insideR (grade + 6) (realHighLarge grade)) :
    completedRealMixedSliceAmbient parameters cellLength reference insideR grade
      (realMixedCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade) state) ∈
      sourceRange parameters grade large := by
  obtain ⟨insideS, axis⟩ := (realMixedDomain_core_iff parameters reference insideR (grade + 6)
    (realHighLarge grade) state).1 inside
  rw [completedRealMixedSliceAmbient_core parameters cellLength reference insideR grade state insideS axis]
  exact Grad.NonlinearRange.fixedSliceMap_constrained_grade_mem parameters cellLength state.2.1
    reference insideR state.1 insideS grade large state.2.2 axis

theorem completedRealMixedSliceAmbient_mem (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    Set.MapsTo (completedRealMixedSliceAmbient parameters cellLength reference insideR grade)
      (realMixedDomain parameters reference insideR (grade + 6) (realHighLarge grade))
      (sourceRange parameters grade large) :=
  mapsTo_closed_of_dense_core
    (realMixedCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade))
    (realMixedCoreEmbed_denseRange parameters reference insideR (grade + 6) (realHighLarge grade))
    _ _ _ (realMixedDomain_isOpen parameters reference insideR (grade + 6) (realHighLarge grade))
    (sourceRange_closed parameters grade large)
    (completedRealMixedSliceAmbient_contDiffOn parameters cellLength reference insideR grade).continuousOn
    (completedRealMixedSliceAmbient_core_mem parameters cellLength reference insideR grade large)

/-- Literal Q24 with moving real seed, curvature and constrained reference
state, valued in the original real quotient carrier. Only the codomain is
restricted, after proving actual membership on the full open domain. -/
def completedRealMixedSlice (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade) →
      sourceRange parameters grade large :=
  exactRangeRestriction (completedRealMixedSliceAmbient parameters cellLength reference insideR grade)
    (realMixedDomain parameters reference insideR (grade + 6) (realHighLarge grade))
    (sourceRange parameters grade large)
    (completedRealMixedSliceAmbient_mem parameters cellLength reference insideR grade large)

theorem completedRealMixedSlice_inclusion (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (state : RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
    (inside : state ∈ realMixedDomain parameters reference insideR (grade + 6) (realHighLarge grade)) :
    sourceInclusion parameters grade large
      (completedRealMixedSlice parameters cellLength reference insideR grade large state) =
      completedRealMixedSliceAmbient parameters cellLength reference insideR grade state :=
  exactRangeRestriction_coe _ _ _ _ state inside

theorem completedRealMixedSlice_contDiffOn (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    ContDiffOn ℝ ∞ (completedRealMixedSlice parameters cellLength reference insideR grade large)
      (realMixedDomain parameters reference insideR (grade + 6) (realHighLarge grade)) :=
  exactRangeRestriction_contDiffOn _ _ _ _ (sourceRetraction parameters grade large)
    (sourceRetraction_fixes parameters grade large)
    (completedRealMixedSliceAmbient_contDiffOn parameters cellLength reference insideR grade)

theorem completedRealMixedSlice_core (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (state : RealMixedCore parameters reference insideR) (insideS : state.1 ∈ Seed.parameterDomain)
    (axis : ChartAxisCondition (smoothingChartCore parameters state.2.2.val)) :
    sourceInclusion parameters grade large
      (completedRealMixedSlice parameters cellLength reference insideR grade large
        (realMixedCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade) state)) =
      quotientEta parameters grade (fixedSliceMap parameters cellLength reference insideR state.1 insideS
        (realJointCoreToJoint parameters reference insideR state.2)) := by
  rw [completedRealMixedSlice_inclusion parameters cellLength reference insideR grade large _
    ((realMixedDomain_core_iff parameters reference insideR (grade + 6) (realHighLarge grade) state).2 ⟨insideS, axis⟩)]
  exact completedRealMixedSliceAmbient_core parameters cellLength reference insideR grade state insideS axis

theorem completedRealMixedSlice_derivative_inclusion (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (order : ℕ) (state : RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
    (inside : state ∈ realMixedDomain parameters reference insideR (grade + 6) (realHighLarge grade))
    (directions : Fin order → RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) :
    sourceInclusion parameters grade large (iteratedFDeriv ℝ order
      (completedRealMixedSlice parameters cellLength reference insideR grade large) state directions) =
      iteratedFDeriv ℝ order (completedRealMixedSliceAmbient parameters cellLength reference insideR grade) state directions :=
  exactRangeRestriction_derivative_coe _ _ _ _ (sourceRetraction parameters grade large)
    (sourceRetraction_fixes parameters grade large)
    (realMixedDomain_isOpen parameters reference insideR (grade + 6) (realHighLarge grade))
    (completedRealMixedSliceAmbient_contDiffOn parameters cellLength reference insideR grade)
    order state inside directions

theorem completedRealMixedSlice_derivative_norm (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (order : ℕ) (state : RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
    (inside : state ∈ realMixedDomain parameters reference insideR (grade + 6) (realHighLarge grade))
    (directions : Fin order → RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) :
    ‖iteratedFDeriv ℝ order (completedRealMixedSlice parameters cellLength reference insideR grade large) state directions‖ =
      ‖iteratedFDeriv ℝ order (completedRealMixedSliceAmbient parameters cellLength reference insideR grade) state directions‖ := by
  rw [← sourceInclusion_norm parameters grade large,
    completedRealMixedSlice_derivative_inclusion parameters cellLength reference insideR grade large order state inside directions]

end Grad.Q24Realization
