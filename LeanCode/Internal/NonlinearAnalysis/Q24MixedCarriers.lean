import Q24MovingChart
import Q24RealDerivatives

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1200000

open scoped BigOperators ContDiff

namespace Grad.Q24Realization

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisCore Grad.SmoothingFamily Grad.RealFixedRanges

/-- The literal sum of the four finite seed-coordinate absolute values. -/
abbrev SeedL1 := PiLp 1 (fun _ : Fin 4 => ℝ)

def seedL1Equiv : SeedL1 ≃L[ℝ] Seed.Parameters :=
  PiLp.continuousLinearEquiv 1 ℝ (fun _ : Fin 4 => ℝ)

/-- Seed-coordinate sum, curvature norm and the original state sum norm. -/
abbrev MixedAmbient (parameters : PhaseParameters) (grade : ℕ) :=
  WithLp 1 (SeedL1 × JointAmbient parameters grade)

def mixedSeed (parameters : PhaseParameters) (grade : ℕ) :
    MixedAmbient parameters grade →L[ℝ] Seed.Parameters :=
  seedL1Equiv.toContinuousLinearMap.comp
    ((ContinuousLinearMap.fst ℝ SeedL1 (JointAmbient parameters grade)).comp
      (WithLp.prodContinuousLinearEquiv 1 ℝ SeedL1 (JointAmbient parameters grade)).toContinuousLinearMap)

def mixedJoint (parameters : PhaseParameters) (grade : ℕ) :
    MixedAmbient parameters grade →L[ℝ] JointAmbient parameters grade :=
  (ContinuousLinearMap.snd ℝ SeedL1 (JointAmbient parameters grade)).comp
    (WithLp.prodContinuousLinearEquiv 1 ℝ SeedL1 (JointAmbient parameters grade)).toContinuousLinearMap

def mixedStatePair (parameters : PhaseParameters) (grade : ℕ)
    (state : MixedAmbient parameters grade) : Seed.Parameters × XAmbient parameters grade :=
  (mixedSeed parameters grade state, (mixedJoint parameters grade state).ofLp.2)

theorem mixedStatePair_contDiff (parameters : PhaseParameters) (grade : ℕ) :
    ContDiff ℝ ∞ (mixedStatePair parameters grade) :=
  (mixedSeed parameters grade).contDiff.prodMk
    ((WithLp.prodContinuousLinearEquiv 1 ℝ ℂ (XAmbient parameters grade)).contDiff.snd.comp
      (mixedJoint parameters grade).contDiff)

def mixedDomain (parameters : PhaseParameters) (grade : ℕ) : Set (MixedAmbient parameters grade) :=
  {state | mixedSeed parameters grade state ∈ Seed.parameterDomain ∧
    mixedJoint parameters grade state ∈ jointDomain parameters grade}

theorem mixedDomain_isOpen (parameters : PhaseParameters) (grade : ℕ) :
    IsOpen (mixedDomain parameters grade) :=
  (Seed.parameterDomain_isOpen.preimage (mixedSeed parameters grade).continuous).inter
    ((jointDomain_isOpen parameters grade).preimage (mixedJoint parameters grade).continuous)

def mixedCoreEmbed (parameters : PhaseParameters) (grade : ℕ)
    (state : Seed.Parameters × JointState parameters) : MixedAmbient parameters grade :=
  WithLp.toLp 1 (WithLp.toLp 1 state.1, jointCoreEmbed parameters grade state.2)

theorem mixedCoreEmbed_norm (parameters : PhaseParameters) (grade : ℕ)
    (state : Seed.Parameters × JointState parameters) :
    ‖mixedCoreEmbed parameters grade state‖ = (∑ coordinate, |state.1 coordinate|) + jointNorm grade state.2 := by
  rw [mixedCoreEmbed, WithLp.prod_norm_eq_of_L1]
  change ‖(WithLp.toLp 1 state.1 : SeedL1)‖ + ‖jointCoreEmbed parameters grade state.2‖ = _
  rw [PiLp.norm_eq_of_L1, jointCoreEmbed_norm]
  simp only [Real.norm_eq_abs]

theorem mixedCoreEmbed_denseRange (parameters : PhaseParameters) (grade : ℕ) :
    DenseRange (mixedCoreEmbed parameters grade) :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ SeedL1 (JointAmbient parameters grade)).symm.surjective.denseRange.comp
    (seedL1Equiv.symm.surjective.denseRange.prodMap (jointCoreEmbed_denseRange parameters grade))
    (WithLp.prodContinuousLinearEquiv 1 ℝ SeedL1 (JointAmbient parameters grade)).symm.continuous

theorem mixedDomain_core_iff (parameters : PhaseParameters) (grade : ℕ)
    (state : Seed.Parameters × JointState parameters) :
    mixedCoreEmbed parameters grade state ∈ mixedDomain parameters grade ↔
      state.1 ∈ Seed.parameterDomain ∧ ChartAxisCondition state.2.2 := by
  change state.1 ∈ Seed.parameterDomain ∧ jointCoreEmbed parameters grade state.2 ∈ jointDomain parameters grade ↔ _
  rw [jointDomain_core_iff]

def mixedLowering {lower upper : ℕ} (parameters : PhaseParameters) (ordered : lower ≤ upper) :
    MixedAmbient parameters upper →L[ℝ] MixedAmbient parameters lower :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ SeedL1 (JointAmbient parameters lower)).symm.toContinuousLinearMap.comp
    (((ContinuousLinearMap.id ℝ SeedL1).prodMap (jointLowering parameters ordered)).comp
      (WithLp.prodContinuousLinearEquiv 1 ℝ SeedL1 (JointAmbient parameters upper)).toContinuousLinearMap)

theorem mixedLowering_core {lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (state : Seed.Parameters × JointState parameters) :
    mixedLowering parameters ordered (mixedCoreEmbed parameters upper state) = mixedCoreEmbed parameters lower state := by
  change WithLp.toLp 1 (WithLp.toLp 1 state.1,
    jointLowering parameters ordered (jointCoreEmbed parameters upper state.2)) = _
  rw [jointLowering_core]
  rfl

theorem mixedLowering_norm_le {lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (state : MixedAmbient parameters upper) :
    ‖mixedLowering parameters ordered state‖ ≤ ‖state‖ := by
  rw [WithLp.prod_norm_eq_of_L1 (mixedLowering parameters ordered state), WithLp.prod_norm_eq_of_L1 state]
  exact add_le_add le_rfl (jointLowering_norm_le parameters ordered state.ofLp.2)

theorem mixedLowering_domain_iff {lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (state : MixedAmbient parameters upper) :
    mixedLowering parameters ordered state ∈ mixedDomain parameters lower ↔
      state ∈ mixedDomain parameters upper := by
  change mixedSeed parameters upper state ∈ Seed.parameterDomain ∧
    jointLowering parameters ordered (mixedJoint parameters upper state) ∈ jointDomain parameters lower ↔ _
  rw [jointLowering_domain_iff]
  rfl

end Grad.Q24Realization
