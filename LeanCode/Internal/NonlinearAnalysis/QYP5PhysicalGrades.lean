import QYP4PhysicalCodomain
import Q24RealMixedGrades

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 600000

open scoped ContDiff

namespace Grad.PhysicalCoordinates

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.Q24Realization Grad.RealFixedRanges Grad.ConstrainedGrades

theorem completedPhysicalMixedSlice_gradeCompatibility {lower upper : ℕ}
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (ordered : lower ≤ upper) (state : MixedAmbient parameters (upper + 6))
    (inside : state ∈ mixedDomain parameters (upper + 6)) :
    zLowering parameters ordered
      (completedPhysicalMixedSlice parameters cellLength reference upper state) =
    completedPhysicalMixedSlice parameters cellLength reference lower
      (mixedLowering parameters (Nat.add_le_add_right ordered 6) state) := by
  apply eq_on_open_of_dense (mixedCoreEmbed parameters (upper + 6))
    (mixedCoreEmbed_denseRange parameters (upper + 6)) (mixedDomain parameters (upper + 6))
    (mixedDomain_isOpen parameters (upper + 6))
    (fun value => zLowering parameters ordered
      (completedPhysicalMixedSlice parameters cellLength reference upper value))
    (fun value => completedPhysicalMixedSlice parameters cellLength reference lower
      (mixedLowering parameters (Nat.add_le_add_right ordered 6) value))
  · exact (zLowering parameters ordered).continuous.comp_continuousOn
      (completedPhysicalMixedSlice_contDiffOn parameters cellLength reference upper).continuousOn
  · exact (completedPhysicalMixedSlice_contDiffOn parameters cellLength reference lower).continuousOn.comp
      (mixedLowering parameters (Nat.add_le_add_right ordered 6)).continuous.continuousOn
      (fun value member => (mixedLowering_domain_iff parameters (Nat.add_le_add_right ordered 6) value).2 member)
  · intro core member
    obtain ⟨insideS, axis⟩ := (mixedDomain_core_iff parameters (upper + 6) core).1 member
    rw [completedPhysicalMixedSlice_core parameters cellLength reference insideR upper core insideS axis,
      zLowering_core, mixedLowering_core,
      completedPhysicalMixedSlice_core parameters cellLength reference insideR lower core insideS axis]
  · exact inside


theorem completedPhysicalMixedSlice_derivative_gradeCompatibility {lower upper : ℕ}
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (ordered : lower ≤ upper) (order : ℕ) (state : MixedAmbient parameters (upper + 6))
    (inside : state ∈ mixedDomain parameters (upper + 6))
    (directions : Fin order → MixedAmbient parameters (upper + 6)) :
    zLowering parameters ordered
      (iteratedFDeriv ℝ order (completedPhysicalMixedSlice parameters cellLength reference upper) state directions) =
    iteratedFDeriv ℝ order (completedPhysicalMixedSlice parameters cellLength reference lower)
      (mixedLowering parameters (Nat.add_le_add_right ordered 6) state)
      (fun position => mixedLowering parameters (Nat.add_le_add_right ordered 6) (directions position)) := by
  exact derivative_compatibility_on_open
    (mixedLowering parameters (Nat.add_le_add_right ordered 6)) ((zLowering parameters ordered).restrictScalars ℝ)
    (completedPhysicalMixedSlice parameters cellLength reference upper) (completedPhysicalMixedSlice parameters cellLength reference lower)
    (mixedDomain parameters (upper + 6)) (mixedDomain parameters (lower + 6))
    (mixedDomain_isOpen parameters (upper + 6)) (mixedDomain_isOpen parameters (lower + 6))
    (fun value member => (mixedLowering_domain_iff parameters (Nat.add_le_add_right ordered 6) value).2 member)
    (completedPhysicalMixedSlice_contDiffOn parameters cellLength reference upper)
    (completedPhysicalMixedSlice_contDiffOn parameters cellLength reference lower)
    (completedPhysicalMixedSlice_gradeCompatibility parameters cellLength reference insideR ordered) order state inside directions

theorem completedRealPhysicalMixedSliceAmbient_derivative (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade order : ℕ)
    (base : RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
    (inside : base ∈ realMixedDomain parameters reference insideR (grade + 6) (realHighLarge grade))
    (directions : Fin order → RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) :
    iteratedFDeriv ℝ order (completedRealPhysicalMixedSliceAmbient parameters cellLength reference insideR grade)
      base directions =
    iteratedFDeriv ℝ order (completedPhysicalMixedSlice parameters cellLength reference grade)
      (realMixedInclusion parameters reference insideR (grade + 6) (realHighLarge grade) base)
      (fun position => realMixedInclusion parameters reference insideR (grade + 6) (realHighLarge grade) (directions position)) := by
  let : NormedSpace ℝ (RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) := inferInstance
  exact iteratedFDeriv_precomp_on_open
    (realMixedInclusion parameters reference insideR (grade + 6) (realHighLarge grade))
    (completedPhysicalMixedSlice parameters cellLength reference grade) (mixedDomain parameters (grade + 6))
    (mixedDomain_isOpen parameters (grade + 6)) (completedPhysicalMixedSlice_contDiffOn parameters cellLength reference grade)
    order base inside directions

theorem completedRealPhysicalMixedSliceAmbient_gradeCompatibility {lower upper : ℕ}
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (ordered : lower ≤ upper)
    (state : RealMixedAmbient parameters reference insideR (upper + 6) (realHighLarge upper))
    (inside : state ∈ realMixedDomain parameters reference insideR (upper + 6) (realHighLarge upper)) :
    zLowering parameters ordered (completedRealPhysicalMixedSliceAmbient parameters cellLength reference insideR upper state) =
    completedRealPhysicalMixedSliceAmbient parameters cellLength reference insideR lower
      (realMixedLowering parameters reference insideR (realHighLarge lower) (Nat.add_le_add_right ordered 6) state) := by
  unfold completedRealPhysicalMixedSliceAmbient
  rw [realMixedLowering_inclusion]
  exact completedPhysicalMixedSlice_gradeCompatibility parameters cellLength reference insideR ordered _ inside

theorem completedRealPhysicalMixedSliceAmbient_derivative_gradeCompatibility {lower upper : ℕ}
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (ordered : lower ≤ upper) (order : ℕ)
    (state : RealMixedAmbient parameters reference insideR (upper + 6) (realHighLarge upper))
    (inside : state ∈ realMixedDomain parameters reference insideR (upper + 6) (realHighLarge upper))
    (directions : Fin order → RealMixedAmbient parameters reference insideR (upper + 6) (realHighLarge upper)) :
    zLowering parameters ordered
      (iteratedFDeriv ℝ order (completedRealPhysicalMixedSliceAmbient parameters cellLength reference insideR upper) state directions) =
    iteratedFDeriv ℝ order (completedRealPhysicalMixedSliceAmbient parameters cellLength reference insideR lower)
      (realMixedLowering parameters reference insideR (realHighLarge lower) (Nat.add_le_add_right ordered 6) state)
      (fun position => realMixedLowering parameters reference insideR (realHighLarge lower)
        (Nat.add_le_add_right ordered 6) (directions position)) := by
  let : NormedSpace ℝ (RealMixedAmbient parameters reference insideR (upper + 6) (realHighLarge upper)) := inferInstance
  let : NormedSpace ℝ (RealMixedAmbient parameters reference insideR (lower + 6) (realHighLarge lower)) := inferInstance
  exact derivative_compatibility_on_open
    (realMixedLowering parameters reference insideR (realHighLarge lower) (Nat.add_le_add_right ordered 6))
    ((zLowering parameters ordered).restrictScalars ℝ)
    (completedRealPhysicalMixedSliceAmbient parameters cellLength reference insideR upper)
    (completedRealPhysicalMixedSliceAmbient parameters cellLength reference insideR lower)
    (realMixedDomain parameters reference insideR (upper + 6) (realHighLarge upper))
    (realMixedDomain parameters reference insideR (lower + 6) (realHighLarge lower))
    (realMixedDomain_isOpen parameters reference insideR (upper + 6) (realHighLarge upper))
    (realMixedDomain_isOpen parameters reference insideR (lower + 6) (realHighLarge lower))
    (fun value member => (realMixedLowering_domain_iff parameters reference insideR
      (realHighLarge lower) (Nat.add_le_add_right ordered 6) value).2 member)
    (completedRealPhysicalMixedSliceAmbient_contDiffOn parameters cellLength reference insideR upper)
    (completedRealPhysicalMixedSliceAmbient_contDiffOn parameters cellLength reference insideR lower)
    (completedRealPhysicalMixedSliceAmbient_gradeCompatibility parameters cellLength reference insideR ordered)
    order state inside directions

theorem completedRealPhysicalMixedSlice_gradeCompatibility {lower upper : ℕ}
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (state : RealMixedAmbient parameters reference insideR (upper + 6) (realHighLarge upper))
    (inside : state ∈ realMixedDomain parameters reference insideR (upper + 6) (realHighLarge upper)) :
    sourceLowering parameters large ordered
      (completedRealPhysicalMixedSlice parameters cellLength reference insideR upper (large.trans ordered) state) =
      completedRealPhysicalMixedSlice parameters cellLength reference insideR lower large
        (realMixedLowering parameters reference insideR (realHighLarge lower)
          (Nat.add_le_add_right ordered 6) state) := by
  apply Subtype.ext
  have loweredInside := (realMixedLowering_domain_iff parameters reference insideR (realHighLarge lower)
    (Nat.add_le_add_right ordered 6) state).2 inside
  change zLowering parameters ordered (sourceInclusion parameters upper (large.trans ordered)
    (completedRealPhysicalMixedSlice parameters cellLength reference insideR upper (large.trans ordered) state)) =
    sourceInclusion parameters lower large (completedRealPhysicalMixedSlice parameters cellLength reference insideR lower large
      (realMixedLowering parameters reference insideR (realHighLarge lower)
        (Nat.add_le_add_right ordered 6) state))
  rw [completedRealPhysicalMixedSlice_inclusion parameters cellLength reference insideR upper (large.trans ordered) state inside,
    completedRealPhysicalMixedSlice_inclusion parameters cellLength reference insideR lower large _ loweredInside]
  exact completedRealPhysicalMixedSliceAmbient_gradeCompatibility parameters cellLength reference insideR ordered state inside

theorem completedRealPhysicalMixedSlice_derivative_gradeCompatibility {lower upper : ℕ}
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (large : 3 ≤ lower) (ordered : lower ≤ upper) (order : ℕ)
    (state : RealMixedAmbient parameters reference insideR (upper + 6) (realHighLarge upper))
    (inside : state ∈ realMixedDomain parameters reference insideR (upper + 6) (realHighLarge upper))
    (directions : Fin order → RealMixedAmbient parameters reference insideR (upper + 6) (realHighLarge upper)) :
    sourceLowering parameters large ordered (iteratedFDeriv ℝ order
      (completedRealPhysicalMixedSlice parameters cellLength reference insideR upper (large.trans ordered)) state directions) =
    iteratedFDeriv ℝ order (completedRealPhysicalMixedSlice parameters cellLength reference insideR lower large)
      (realMixedLowering parameters reference insideR (realHighLarge lower) (Nat.add_le_add_right ordered 6) state)
      (fun position => realMixedLowering parameters reference insideR (realHighLarge lower)
        (Nat.add_le_add_right ordered 6) (directions position)) := by
  let : NormedSpace ℝ (RealMixedAmbient parameters reference insideR (upper + 6) (realHighLarge upper)) := inferInstance
  let : NormedSpace ℝ (RealMixedAmbient parameters reference insideR (lower + 6) (realHighLarge lower)) := inferInstance
  exact derivative_compatibility_on_open
    (realMixedLowering parameters reference insideR (realHighLarge lower) (Nat.add_le_add_right ordered 6))
    (sourceLowering parameters large ordered)
    (completedRealPhysicalMixedSlice parameters cellLength reference insideR upper (large.trans ordered))
    (completedRealPhysicalMixedSlice parameters cellLength reference insideR lower large)
    (realMixedDomain parameters reference insideR (upper + 6) (realHighLarge upper))
    (realMixedDomain parameters reference insideR (lower + 6) (realHighLarge lower))
    (realMixedDomain_isOpen parameters reference insideR (upper + 6) (realHighLarge upper))
    (realMixedDomain_isOpen parameters reference insideR (lower + 6) (realHighLarge lower))
    (fun value member => (realMixedLowering_domain_iff parameters reference insideR
      (realHighLarge lower) (Nat.add_le_add_right ordered 6) value).2 member)
    (completedRealPhysicalMixedSlice_contDiffOn parameters cellLength reference insideR upper (large.trans ordered))
    (completedRealPhysicalMixedSlice_contDiffOn parameters cellLength reference insideR lower large)
    (completedRealPhysicalMixedSlice_gradeCompatibility parameters cellLength reference insideR large ordered)
    order state inside directions

end Grad.PhysicalCoordinates

