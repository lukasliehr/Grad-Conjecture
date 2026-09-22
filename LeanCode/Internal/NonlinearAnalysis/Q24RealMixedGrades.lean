import Q24RealMixed
import Q24MixedCompatibility

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1600000

open scoped ContDiff

namespace Grad.Q24Realization

open Grad.CartesianState Grad.Constraints Grad.ConstrainedGrades

def realMixedLowering {lower upper : ℕ} (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (large : 3 ≤ lower) (ordered : lower ≤ upper) :
    RealMixedAmbient parameters reference insideR upper (large.trans ordered) →L[ℝ]
      RealMixedAmbient parameters reference insideR lower large :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ SeedL1
    (RealJointAmbient parameters reference insideR lower large)).symm.toContinuousLinearMap.comp
    (((ContinuousLinearMap.id ℝ SeedL1).prodMap
      (realJointLowering parameters reference insideR large ordered)).comp
      (WithLp.prodContinuousLinearEquiv 1 ℝ SeedL1
        (RealJointAmbient parameters reference insideR upper (large.trans ordered))).toContinuousLinearMap)

theorem realMixedLowering_inclusion {lower upper : ℕ} (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (state : RealMixedAmbient parameters reference insideR upper (large.trans ordered)) :
    realMixedInclusion parameters reference insideR lower large
      (realMixedLowering parameters reference insideR large ordered state) =
    mixedLowering parameters ordered
      (realMixedInclusion parameters reference insideR upper (large.trans ordered) state) := rfl

theorem realMixedLowering_norm_le {lower upper : ℕ} (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (state : RealMixedAmbient parameters reference insideR upper (large.trans ordered)) :
    ‖realMixedLowering parameters reference insideR large ordered state‖ ≤ ‖state‖ := by
  rw [← realMixedInclusion_norm parameters reference insideR lower large,
    realMixedLowering_inclusion]
  exact (mixedLowering_norm_le parameters ordered _).trans_eq
    (realMixedInclusion_norm parameters reference insideR upper (large.trans ordered) state)

theorem realMixedLowering_domain_iff {lower upper : ℕ} (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (state : RealMixedAmbient parameters reference insideR upper (large.trans ordered)) :
    realMixedLowering parameters reference insideR large ordered state ∈
      realMixedDomain parameters reference insideR lower large ↔
    state ∈ realMixedDomain parameters reference insideR upper (large.trans ordered) := by
  change realMixedInclusion parameters reference insideR lower large
    (realMixedLowering parameters reference insideR large ordered state) ∈ mixedDomain parameters lower ↔ _
  rw [realMixedLowering_inclusion, mixedLowering_domain_iff]
  rfl

theorem completedRealMixedSliceAmbient_derivative (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade order : ℕ)
    (base : RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
    (inside : base ∈ realMixedDomain parameters reference insideR (grade + 6) (realHighLarge grade))
    (directions : Fin order → RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) :
    iteratedFDeriv ℝ order (completedRealMixedSliceAmbient parameters cellLength reference insideR grade)
      base directions =
    iteratedFDeriv ℝ order (completedMixedSlice parameters cellLength reference grade)
      (realMixedInclusion parameters reference insideR (grade + 6) (realHighLarge grade) base)
      (fun position => realMixedInclusion parameters reference insideR (grade + 6) (realHighLarge grade) (directions position)) := by
  let : NormedSpace ℝ (RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) := inferInstance
  exact iteratedFDeriv_precomp_on_open
    (realMixedInclusion parameters reference insideR (grade + 6) (realHighLarge grade))
    (completedMixedSlice parameters cellLength reference grade) (mixedDomain parameters (grade + 6))
    (mixedDomain_isOpen parameters (grade + 6)) (completedMixedSlice_contDiffOn parameters cellLength reference grade)
    order base inside directions

theorem completedRealMixedSliceAmbient_gradeCompatibility {lower upper : ℕ}
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (ordered : lower ≤ upper)
    (state : RealMixedAmbient parameters reference insideR (upper + 6) (realHighLarge upper))
    (inside : state ∈ realMixedDomain parameters reference insideR (upper + 6) (realHighLarge upper)) :
    zLowering parameters ordered (completedRealMixedSliceAmbient parameters cellLength reference insideR upper state) =
    completedRealMixedSliceAmbient parameters cellLength reference insideR lower
      (realMixedLowering parameters reference insideR (realHighLarge lower) (Nat.add_le_add_right ordered 6) state) := by
  unfold completedRealMixedSliceAmbient
  rw [realMixedLowering_inclusion]
  exact completedMixedSlice_gradeCompatibility parameters cellLength reference insideR ordered _ inside

theorem completedRealMixedSliceAmbient_derivative_gradeCompatibility {lower upper : ℕ}
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (ordered : lower ≤ upper) (order : ℕ)
    (state : RealMixedAmbient parameters reference insideR (upper + 6) (realHighLarge upper))
    (inside : state ∈ realMixedDomain parameters reference insideR (upper + 6) (realHighLarge upper))
    (directions : Fin order → RealMixedAmbient parameters reference insideR (upper + 6) (realHighLarge upper)) :
    zLowering parameters ordered
      (iteratedFDeriv ℝ order (completedRealMixedSliceAmbient parameters cellLength reference insideR upper) state directions) =
    iteratedFDeriv ℝ order (completedRealMixedSliceAmbient parameters cellLength reference insideR lower)
      (realMixedLowering parameters reference insideR (realHighLarge lower) (Nat.add_le_add_right ordered 6) state)
      (fun position => realMixedLowering parameters reference insideR (realHighLarge lower)
        (Nat.add_le_add_right ordered 6) (directions position)) := by
  let : NormedSpace ℝ (RealMixedAmbient parameters reference insideR (upper + 6) (realHighLarge upper)) := inferInstance
  let : NormedSpace ℝ (RealMixedAmbient parameters reference insideR (lower + 6) (realHighLarge lower)) := inferInstance
  exact derivative_compatibility_on_open
    (realMixedLowering parameters reference insideR (realHighLarge lower) (Nat.add_le_add_right ordered 6))
    ((zLowering parameters ordered).restrictScalars ℝ)
    (completedRealMixedSliceAmbient parameters cellLength reference insideR upper)
    (completedRealMixedSliceAmbient parameters cellLength reference insideR lower)
    (realMixedDomain parameters reference insideR (upper + 6) (realHighLarge upper))
    (realMixedDomain parameters reference insideR (lower + 6) (realHighLarge lower))
    (realMixedDomain_isOpen parameters reference insideR (upper + 6) (realHighLarge upper))
    (realMixedDomain_isOpen parameters reference insideR (lower + 6) (realHighLarge lower))
    (fun value member => (realMixedLowering_domain_iff parameters reference insideR
      (realHighLarge lower) (Nat.add_le_add_right ordered 6) value).2 member)
    (completedRealMixedSliceAmbient_contDiffOn parameters cellLength reference insideR upper)
    (completedRealMixedSliceAmbient_contDiffOn parameters cellLength reference insideR lower)
    (completedRealMixedSliceAmbient_gradeCompatibility parameters cellLength reference insideR ordered)
    order state inside directions

end Grad.Q24Realization
