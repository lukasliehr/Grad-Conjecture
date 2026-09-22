import QY10MixedDirectional

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

open scoped BigOperators ContDiff

namespace Grad.Q24Realization

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisCore Grad.SmoothingFamily Grad.ConstrainedGrades

private theorem continuous_fiber_majorant {B E D : Type*}
    [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace D]
    (fiber : B → E) (fiberContinuous : Continuous fiber)
    (majorant : E × D → ℝ) (majorantContinuous : Continuous majorant) (constant : ℝ) :
    Continuous (fun pair : B × D => constant * majorant (fiber pair.1, pair.2)) :=
  continuous_const.mul (majorantContinuous.comp
    ((fiberContinuous.comp continuous_fst).prodMk continuous_snd))

/-- The actual Q24 completion step for a supplied, proved mixed core
estimate. Finite seed and curvature are held fixed throughout density.
This adapter does not assert the missing Q23 core estimate. -/
theorem completedMixedSlice_bound_of_core
    (parameters : PhaseParameters) (cellLength : ℝ) (reference : Seed.Parameters)
    (grade order : ℕ) (seedPatch : Set Seed.Parameters) (curvatureBound stateBound constant : ℝ)
    (coreBound : ∀ (base : Seed.Parameters × JointState parameters)
      (directions : Fin order → Seed.Parameters × JointState parameters),
      base.1 ∈ seedPatch → ‖base.2.1‖ ≤ curvatureBound →
      mixedCoreEmbed parameters (grade + 6) base ∈ mixedDomain parameters (grade + 6) →
      chartStateNorm 4 base.2.2 ≤ stateBound + 1 →
      ‖iteratedFDeriv ℝ order (completedMixedSlice parameters cellLength reference grade)
        (mixedCoreEmbed parameters (grade + 6) base)
        (fun position => mixedCoreEmbed parameters (grade + 6) (directions position))‖ ≤
      constant * mixedCompletedOneHigh parameters grade order (mixedCoreEmbed parameters (grade + 6) base)
        (fun position => mixedCoreEmbed parameters (grade + 6) (directions position)))
    (base : MixedAmbient parameters (grade + 6))
    (directions : Fin order → MixedAmbient parameters (grade + 6))
    (inPatch : mixedSeed parameters (grade + 6) base ∈ seedPatch)
    (curvature : ‖(mixedJoint parameters (grade + 6) base).ofLp.1‖ ≤ curvatureBound)
    (inside : base ∈ mixedDomain parameters (grade + 6))
    (bounded : ‖xLowering parameters (realLowLeHigh grade) (mixedStatePart parameters (grade + 6) base)‖ ≤ stateBound) :
    ‖iteratedFDeriv ℝ order (completedMixedSlice parameters cellLength reference grade) base directions‖ ≤
      constant * mixedCompletedOneHigh parameters grade order base directions := by
  let : NormedSpace ℝ (XAmbient parameters (grade + 6)) := inferInstance
  let : NormedSpace ℝ (MixedAmbient parameters (grade + 6)) := inferInstance
  let : NormedSpace ℝ (ZAmbient parameters grade) := inferInstance
  let seed := mixedSeed parameters (grade + 6) base
  let epsilon := (mixedJoint parameters (grade + 6) base).ofLp.1
  let fiber := mixedStateFiber parameters (grade + 6) seed epsilon
  have fiberContinuous := mixedStateFiber_continuous parameters (grade + 6) seed epsilon
  have majorantContinuous : Continuous (fun pair : XAmbient parameters (grade + 6) ×
      (Fin order → MixedAmbient parameters (grade + 6)) =>
      constant * mixedCompletedOneHigh parameters grade order (fiber pair.1) pair.2) :=
    continuous_fiber_majorant (B := XAmbient parameters (grade + 6))
      (E := MixedAmbient parameters (grade + 6))
      (D := Fin order → MixedAmbient parameters (grade + 6))
      fiber fiberContinuous
      (fun pair => mixedCompletedOneHigh parameters grade order pair.1 pair.2)
      (mixedCompletedOneHigh_continuous parameters grade order) constant
  have identity : fiber (mixedStatePart parameters (grade + 6) base) = base :=
    mixedStateFiber_reconstruct parameters (grade + 6) base
  suffices estimate : ‖iteratedFDeriv ℝ order (completedMixedSlice parameters cellLength reference grade)
      (fiber (mixedStatePart parameters (grade + 6) base)) directions‖ ≤
      constant * mixedCompletedOneHigh parameters grade order
        (fiber (mixedStatePart parameters (grade + 6) base)) directions by
    simpa only [identity] using estimate
  apply derivative_bound_on_dense_fiber
    (C := ChartState parameters) (D := Seed.Parameters × JointState parameters)
    (B := XAmbient parameters (grade + 6)) (E := MixedAmbient parameters (grade + 6))
    (F := ZAmbient parameters grade)
    (chartCoreEmbed parameters (grade + 6)) (chartCoreEmbed_denseRange parameters (grade + 6))
    (mixedCoreEmbed parameters (grade + 6)) (mixedCoreEmbed_denseRange parameters (grade + 6))
    fiber fiberContinuous (completedMixedSlice parameters cellLength reference grade)
    (mixedDomain parameters (grade + 6)) (mixedDomain_isOpen parameters (grade + 6))
    (completedMixedSlice_contDiffOn parameters cellLength reference grade) order
    (fun state => ‖xLowering parameters (realLowLeHigh grade) state‖)
    (xLowering parameters (realLowLeHigh grade)).continuous.norm (stateBound + 1)
    (fun pair => constant * mixedCompletedOneHigh parameters grade order (fiber pair.1) pair.2)
    majorantContinuous
  · intro state tuple member low
    change mixedCoreEmbed parameters (grade + 6) (seed, epsilon, state) ∈ mixedDomain parameters (grade + 6) at member
    change ‖xLowering parameters (realLowLeHigh grade) (chartCoreEmbed parameters (grade + 6) state)‖ < _ at low
    rw [xLowering_chartCore, chartCoreEmbed_norm] at low
    exact coreBound (seed, epsilon, state) tuple inPatch curvature member low.le
  · rwa [identity]
  · exact bounded.trans_lt (lt_add_one stateBound)

end Grad.Q24Realization
