import QY8FiberDensity

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.Q24Realization

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.RealFixedRanges Grad.AxisCore Grad.ConstrainedGrades
open Grad.SmoothingFamily

def mixedCoreLinear (parameters : PhaseParameters) (grade : ℕ) :
    (Seed.Parameters × JointState parameters) →ₗ[ℝ] MixedAmbient parameters grade :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ SeedL1 (JointAmbient parameters grade)).symm.toLinearMap.comp
    (seedL1Equiv.symm.toLinearMap.prodMap ((jointCoreLinear parameters grade).restrictScalars ℝ))

theorem mixedCoreLinear_apply (parameters : PhaseParameters) (grade : ℕ)
    (state : Seed.Parameters × JointState parameters) :
    mixedCoreLinear parameters grade state = mixedCoreEmbed parameters grade state := rfl

/-- Extract only the infinite-dimensional state: seed and curvature never
contribute to the high base-state factor in Q23. -/
def mixedStatePart (parameters : PhaseParameters) (grade : ℕ) :
    MixedAmbient parameters grade →L[ℝ] XAmbient parameters grade :=
  (ContinuousLinearMap.snd ℝ ℂ (XAmbient parameters grade)).comp
    ((WithLp.prodContinuousLinearEquiv 1 ℝ ℂ (XAmbient parameters grade)).toContinuousLinearMap.comp
      (mixedJoint parameters grade))

theorem mixedStatePart_core (parameters : PhaseParameters) (grade : ℕ)
    (state : Seed.Parameters × JointState parameters) :
    mixedStatePart parameters grade (mixedCoreEmbed parameters grade state) =
      chartCoreEmbed parameters grade state.2.2 := rfl

def mixedCompletedOneHigh (parameters : PhaseParameters) (grade order : ℕ)
    (base : MixedAmbient parameters (grade + 6))
    (directions : Fin order → MixedAmbient parameters (grade + 6)) : ℝ :=
  (1 + ‖mixedStatePart parameters (grade + 6) base‖) *
      ∏ position, ‖mixedLowering parameters (realLowLeHigh grade) (directions position)‖ +
    ∑ position, ‖directions position‖ *
      ∏ other ∈ Finset.univ.erase position,
        ‖mixedLowering parameters (realLowLeHigh grade) (directions other)‖

theorem mixedCompletedOneHigh_core (parameters : PhaseParameters) (grade order : ℕ)
    (base : Seed.Parameters × JointState parameters)
    (directions : Fin order → Seed.Parameters × JointState parameters) :
    mixedCompletedOneHigh parameters grade order (mixedCoreEmbed parameters (grade + 6) base)
      (fun position => mixedCoreEmbed parameters (grade + 6) (directions position)) =
    (1 + chartStateNorm (grade + 6) base.2.2) *
      ∏ position, ((∑ coordinate, |(directions position).1 coordinate|) + jointNorm 4 (directions position).2) +
    ∑ position, ((∑ coordinate, |(directions position).1 coordinate|) + jointNorm (grade + 6) (directions position).2) *
      ∏ other ∈ Finset.univ.erase position,
        ((∑ coordinate, |(directions other).1 coordinate|) + jointNorm 4 (directions other).2) := by
  simp only [mixedCompletedOneHigh, mixedStatePart_core, chartCoreEmbed_norm,
    mixedLowering_core, mixedCoreEmbed_norm]

theorem mixedCompletedOneHigh_continuous (parameters : PhaseParameters) (grade order : ℕ) :
    Continuous (fun pair : MixedAmbient parameters (grade + 6) ×
      (Fin order → MixedAmbient parameters (grade + 6)) =>
        mixedCompletedOneHigh parameters grade order pair.1 pair.2) := by
  unfold mixedCompletedOneHigh
  fun_prop

/-- Embed a varying state while keeping the finite seed and curvature
exactly fixed, suitable even at a boundary point of a compact seed patch. -/
def mixedStateFiber (parameters : PhaseParameters) (grade : ℕ)
    (seed : Seed.Parameters) (epsilon : ℂ) (state : XAmbient parameters grade) : MixedAmbient parameters grade :=
  WithLp.toLp 1 (WithLp.toLp 1 seed, WithLp.toLp 1 (epsilon, state))

theorem mixedStateFiber_continuous (parameters : PhaseParameters) (grade : ℕ)
    (seed : Seed.Parameters) (epsilon : ℂ) : Continuous (mixedStateFiber parameters grade seed epsilon) :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ SeedL1 (JointAmbient parameters grade)).symm.continuous.comp
    (continuous_const.prodMk ((WithLp.prodContinuousLinearEquiv 1 ℝ ℂ (XAmbient parameters grade)).symm.continuous.comp
      (continuous_const.prodMk continuous_id)))

theorem mixedStateFiber_core (parameters : PhaseParameters) (grade : ℕ)
    (seed : Seed.Parameters) (epsilon : ℂ) (state : ChartState parameters) :
    mixedStateFiber parameters grade seed epsilon (chartCoreEmbed parameters grade state) =
      mixedCoreEmbed parameters grade (seed, epsilon, state) := rfl

theorem mixedStateFiber_reconstruct (parameters : PhaseParameters) (grade : ℕ)
    (state : MixedAmbient parameters grade) :
    mixedStateFiber parameters grade (mixedSeed parameters grade state)
      (mixedJoint parameters grade state).ofLp.1 (mixedStatePart parameters grade state) = state := rfl

def realMixedCompletedOneHigh (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade order : ℕ)
    (base : RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
    (directions : Fin order → RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) : ℝ :=
  (1 + ‖base.ofLp.2.ofLp.2‖) *
      ∏ position, ‖realMixedLowering parameters reference insideR realLowLarge (realLowLeHigh grade) (directions position)‖ +
    ∑ position, ‖directions position‖ *
      ∏ other ∈ Finset.univ.erase position,
        ‖realMixedLowering parameters reference insideR realLowLarge (realLowLeHigh grade) (directions other)‖

theorem mixedStatePart_realInclusion (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (state : RealMixedAmbient parameters reference insideR grade large) :
    mixedStatePart parameters grade (realMixedInclusion parameters reference insideR grade large state) =
      stateInclusion parameters reference insideR grade large state.ofLp.2.ofLp.2 := rfl

theorem realMixedCompletedOneHigh_inclusion (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (grade order : ℕ)
    (base : RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
    (directions : Fin order → RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) :
    mixedCompletedOneHigh parameters grade order
      (realMixedInclusion parameters reference insideR (grade + 6) (realHighLarge grade) base)
      (fun position => realMixedInclusion parameters reference insideR (grade + 6) (realHighLarge grade) (directions position)) =
    realMixedCompletedOneHigh parameters reference insideR grade order base directions := by
  simp only [mixedCompletedOneHigh, realMixedCompletedOneHigh, mixedStatePart_realInclusion, stateInclusion_norm,
    ← realMixedLowering_inclusion parameters reference insideR realLowLarge (realLowLeHigh grade), realMixedInclusion_norm]

end Grad.Q24Realization
