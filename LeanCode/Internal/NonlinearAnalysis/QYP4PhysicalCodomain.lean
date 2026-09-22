import QYP3PhysicalMixedMap
import QY5FixedGrades
import Q24RealMixed

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 600000

open scoped ContDiff

namespace Grad.PhysicalCoordinates

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.RealFixedRanges Grad.SmoothingFamily Grad.AxisCore Grad.QuotientProjection
open Grad.Q24Realization

def completedRealPhysicalMixedSliceAmbient (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ)
    (state : RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) :
    ZAmbient parameters grade :=
  completedPhysicalMixedSlice parameters cellLength reference grade
    (realMixedInclusion parameters reference insideR (grade + 6) (realHighLarge grade) state)

theorem completedRealPhysicalMixedSliceAmbient_contDiffOn (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) :
    ContDiffOn ℝ ∞ (completedRealPhysicalMixedSliceAmbient parameters cellLength reference insideR grade)
      (realMixedDomain parameters reference insideR (grade + 6) (realHighLarge grade)) := by
  let : NormedSpace ℝ (RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) := inferInstance
  exact (completedPhysicalMixedSlice_contDiffOn parameters cellLength reference grade).comp_continuousLinearMap
    (G := RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
    (realMixedInclusion parameters reference insideR (grade + 6) (realHighLarge grade))

theorem completedRealPhysicalMixedSliceAmbient_core (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ)
    (state : RealMixedCore parameters reference insideR)
    (insideS : state.1 ∈ Seed.parameterDomain)
    (axis : ChartAxisCondition (smoothingChartCore parameters state.2.2.val)) :
    completedRealPhysicalMixedSliceAmbient parameters cellLength reference insideR grade
      (realMixedCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade) state) =
    Grad.QuotientProjection.quotientEta parameters grade
      (physicalFixedSliceMap parameters cellLength reference insideR state.1 insideS
        (realJointCoreToJoint parameters reference insideR state.2)) := by
  unfold completedRealPhysicalMixedSliceAmbient
  rw [realMixedInclusion_core]
  exact completedPhysicalMixedSlice_core parameters cellLength reference insideR grade _ insideS axis


theorem completedRealPhysicalMixedSliceAmbient_core_mem (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (state : RealMixedCore parameters reference insideR)
    (inside : realMixedCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade) state ∈
      realMixedDomain parameters reference insideR (grade + 6) (realHighLarge grade)) :
    completedRealPhysicalMixedSliceAmbient parameters cellLength reference insideR grade
      (realMixedCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade) state) ∈
      sourceRange parameters grade large := by
  obtain ⟨insideS, axis⟩ := (realMixedDomain_core_iff parameters reference insideR (grade + 6)
    (realHighLarge grade) state).1 inside
  rw [completedRealPhysicalMixedSliceAmbient_core parameters cellLength reference insideR grade state insideS axis]
  exact Grad.PhysicalCoordinates.physicalFixedSliceMap_constrained_grade_mem parameters cellLength state.2.1
    reference insideR state.1 insideS grade large state.2.2 axis

theorem completedRealPhysicalMixedSliceAmbient_mem (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    Set.MapsTo (completedRealPhysicalMixedSliceAmbient parameters cellLength reference insideR grade)
      (realMixedDomain parameters reference insideR (grade + 6) (realHighLarge grade))
      (sourceRange parameters grade large) :=
  mapsTo_closed_of_dense_core
    (realMixedCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade))
    (realMixedCoreEmbed_denseRange parameters reference insideR (grade + 6) (realHighLarge grade))
    _ _ _ (realMixedDomain_isOpen parameters reference insideR (grade + 6) (realHighLarge grade))
    (sourceRange_closed parameters grade large)
    (completedRealPhysicalMixedSliceAmbient_contDiffOn parameters cellLength reference insideR grade).continuousOn
    (completedRealPhysicalMixedSliceAmbient_core_mem parameters cellLength reference insideR grade large)

/-- Literal Q24 with moving real seed, curvature and constrained reference
state, valued in the original real quotient carrier. Only the codomain is
restricted, after proving actual membership on the full open domain. -/
def completedRealPhysicalMixedSlice (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade) →
      sourceRange parameters grade large :=
  exactRangeRestriction (completedRealPhysicalMixedSliceAmbient parameters cellLength reference insideR grade)
    (realMixedDomain parameters reference insideR (grade + 6) (realHighLarge grade))
    (sourceRange parameters grade large)
    (completedRealPhysicalMixedSliceAmbient_mem parameters cellLength reference insideR grade large)

theorem completedRealPhysicalMixedSlice_inclusion (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (state : RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
    (inside : state ∈ realMixedDomain parameters reference insideR (grade + 6) (realHighLarge grade)) :
    sourceInclusion parameters grade large
      (completedRealPhysicalMixedSlice parameters cellLength reference insideR grade large state) =
      completedRealPhysicalMixedSliceAmbient parameters cellLength reference insideR grade state :=
  exactRangeRestriction_coe _ _ _ _ state inside

theorem completedRealPhysicalMixedSlice_contDiffOn (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    ContDiffOn ℝ ∞ (completedRealPhysicalMixedSlice parameters cellLength reference insideR grade large)
      (realMixedDomain parameters reference insideR (grade + 6) (realHighLarge grade)) :=
  exactRangeRestriction_contDiffOn _ _ _ _ (sourceRetraction parameters grade large)
    (sourceRetraction_fixes parameters grade large)
    (completedRealPhysicalMixedSliceAmbient_contDiffOn parameters cellLength reference insideR grade)

theorem completedRealPhysicalMixedSlice_core (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (state : RealMixedCore parameters reference insideR) (insideS : state.1 ∈ Seed.parameterDomain)
    (axis : ChartAxisCondition (smoothingChartCore parameters state.2.2.val)) :
    sourceInclusion parameters grade large
      (completedRealPhysicalMixedSlice parameters cellLength reference insideR grade large
        (realMixedCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade) state)) =
      quotientEta parameters grade (physicalFixedSliceMap parameters cellLength reference insideR state.1 insideS
        (realJointCoreToJoint parameters reference insideR state.2)) := by
  rw [completedRealPhysicalMixedSlice_inclusion parameters cellLength reference insideR grade large _
    ((realMixedDomain_core_iff parameters reference insideR (grade + 6) (realHighLarge grade) state).2 ⟨insideS, axis⟩)]
  exact completedRealPhysicalMixedSliceAmbient_core parameters cellLength reference insideR grade state insideS axis

theorem completedRealPhysicalMixedSlice_derivative_inclusion (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (order : ℕ) (state : RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
    (inside : state ∈ realMixedDomain parameters reference insideR (grade + 6) (realHighLarge grade))
    (directions : Fin order → RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) :
    sourceInclusion parameters grade large (iteratedFDeriv ℝ order
      (completedRealPhysicalMixedSlice parameters cellLength reference insideR grade large) state directions) =
      iteratedFDeriv ℝ order (completedRealPhysicalMixedSliceAmbient parameters cellLength reference insideR grade) state directions :=
  exactRangeRestriction_derivative_coe _ _ _ _ (sourceRetraction parameters grade large)
    (sourceRetraction_fixes parameters grade large)
    (realMixedDomain_isOpen parameters reference insideR (grade + 6) (realHighLarge grade))
    (completedRealPhysicalMixedSliceAmbient_contDiffOn parameters cellLength reference insideR grade)
    order state inside directions

theorem completedRealPhysicalMixedSlice_derivative_norm (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (order : ℕ) (state : RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
    (inside : state ∈ realMixedDomain parameters reference insideR (grade + 6) (realHighLarge grade))
    (directions : Fin order → RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) :
    ‖iteratedFDeriv ℝ order (completedRealPhysicalMixedSlice parameters cellLength reference insideR grade large) state directions‖ =
      ‖iteratedFDeriv ℝ order (completedRealPhysicalMixedSliceAmbient parameters cellLength reference insideR grade) state directions‖ := by
  rw [← sourceInclusion_norm parameters grade large,
    completedRealPhysicalMixedSlice_derivative_inclusion parameters cellLength reference insideR grade large order state inside directions]


end Grad.PhysicalCoordinates

