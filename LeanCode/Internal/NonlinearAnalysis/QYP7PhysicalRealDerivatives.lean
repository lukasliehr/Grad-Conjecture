import QYP6PhysicalDerivativeBridge

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 600000

open scoped BigOperators ContDiff

namespace Grad.PhysicalCoordinates

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.RealFixedRanges Grad.ConstrainedGrades Grad.SmoothingFamily
open Grad.Q24Realization Grad.MixedQuotientComposition Grad.QuotientProjection

theorem completedRealPhysicalMixedSlice_bound_of_ambient
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 3 ≤ grade) (order : ℕ)
    (seedPatch : Set Seed.Parameters) (curvatureBound stateBound constant : ℝ)
    (estimate : ∀ (base : MixedAmbient parameters (grade + 6))
      (directions : Fin order → MixedAmbient parameters (grade + 6)),
      mixedSeed parameters (grade + 6) base ∈ seedPatch →
      ‖(mixedJoint parameters (grade + 6) base).ofLp.1‖ ≤ curvatureBound →
      base ∈ mixedDomain parameters (grade + 6) →
      ‖xLowering parameters (realLowLeHigh grade) (mixedStatePart parameters (grade + 6) base)‖ ≤ stateBound →
      ‖iteratedFDeriv ℝ order (completedPhysicalMixedSlice parameters cellLength reference grade) base directions‖ ≤
        constant * mixedCompletedOneHigh parameters grade order base directions)
    (base : RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
    (directions : Fin order → RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
    (inPatch : realMixedSeed parameters reference insideR (grade + 6) (realHighLarge grade) base ∈ seedPatch)
    (curvature : ‖base.ofLp.2.ofLp.1‖ ≤ curvatureBound)
    (inside : base ∈ realMixedDomain parameters reference insideR (grade + 6) (realHighLarge grade))
    (bounded : ‖stateLowering parameters reference insideR realLowLarge (realLowLeHigh grade) base.ofLp.2.ofLp.2‖ ≤ stateBound) :
    ‖iteratedFDeriv ℝ order (completedRealPhysicalMixedSlice parameters cellLength reference insideR grade large) base directions‖ ≤
      constant * realMixedCompletedOneHigh parameters reference insideR grade order base directions := by
  rw [completedRealPhysicalMixedSlice_derivative_norm parameters cellLength reference insideR grade large order base inside,
    completedRealPhysicalMixedSliceAmbient_derivative parameters cellLength reference insideR grade order base inside,
    ← realMixedCompletedOneHigh_inclusion]
  refine estimate _ _ inPatch ?_ inside ?_
  · change ‖(base.ofLp.2.ofLp.1 : ℂ)‖ ≤ curvatureBound
    simpa only [Complex.norm_real] using curvature
  · rw [mixedStatePart_realInclusion]
    exact bounded

variable {parameters : PhaseParameters}

theorem physicalMixedComposedDerivative_real_core
    (family : (order : ℕ) → Input parameters →
      (Fin order → Input parameters) → QuotientState parameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (zeroth : ∀ (base : Input parameters) (insideS : base.1 ∈ Seed.parameterDomain),
      ChartAxisCondition base.2.2 → ∀ directions,
        family 0 base directions = physicalReferenceState parameters reference insideR base.1 insideS base.2)
    (genuine : ∀ order base (directions : Fin (order + 1) → Input parameters),
      CoreAdmissible base → IsStateDirectionalDerivative
        (fun point => family order point (fun position => directions position.castSucc))
        base (directions (Fin.last order)) (family (order + 1) base directions))
    (cellLength : ℝ) (grade : ℕ) (large : 3 ≤ grade) (order : ℕ)
    (base : RealMixedCore parameters reference insideR) (insideS : base.1 ∈ Seed.parameterDomain)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.2.val))
    (directions : Fin order → RealMixedCore parameters reference insideR) :
    sourceInclusion parameters grade large (iteratedFDeriv ℝ order
      (completedRealPhysicalMixedSlice parameters cellLength reference insideR grade large)
      (realMixedCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade) base)
      (fun position => realMixedCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade)
        (directions position))) =
      quotientEta parameters grade (composedDerivative family cellLength order
        (base.1, realJointCoreToJoint parameters reference insideR base.2)
        (fun position => ((directions position.rev).1,
          realJointCoreToJoint parameters reference insideR (directions position.rev).2))) := by
  have inside := (realMixedDomain_core_iff parameters reference insideR (grade + 6)
    (realHighLarge grade) base).2 ⟨insideS, axis⟩
  rw [completedRealPhysicalMixedSlice_derivative_inclusion parameters cellLength reference insideR grade large order _ inside,
    completedRealPhysicalMixedSliceAmbient_derivative parameters cellLength reference insideR grade order _ inside]
  simp only [realMixedInclusion_core]
  exact physicalMixedComposedDerivative_core family reference insideR zeroth genuine cellLength grade order
    (base.1, realJointCoreToJoint parameters reference insideR base.2) ⟨insideS, axis⟩
    (fun position => ((directions position).1,
      realJointCoreToJoint parameters reference insideR (directions position).2))

/-- Differentiated O21 for every seed/curvature/state direction on the
literal core; fixed-range and reality follow from the exact codomain. -/
theorem physicalMixedComposedDerivative_constrained_mem
    (family : (order : ℕ) → Input parameters →
      (Fin order → Input parameters) → QuotientState parameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (zeroth : ∀ (base : Input parameters) (insideS : base.1 ∈ Seed.parameterDomain),
      ChartAxisCondition base.2.2 → ∀ directions,
        family 0 base directions = physicalReferenceState parameters reference insideR base.1 insideS base.2)
    (genuine : ∀ order base (directions : Fin (order + 1) → Input parameters),
      CoreAdmissible base → IsStateDirectionalDerivative
        (fun point => family order point (fun position => directions position.castSucc))
        base (directions (Fin.last order)) (family (order + 1) base directions))
    (cellLength : ℝ) (order : ℕ)
    (base : RealMixedCore parameters reference insideR) (insideS : base.1 ∈ Seed.parameterDomain)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.2.val))
    (directions : Fin order → RealMixedCore parameters reference insideR) :
    composedDerivative family cellLength order
      (base.1, realJointCoreToJoint parameters reference insideR base.2)
      (fun position => ((directions position).1,
        realJointCoreToJoint parameters reference insideR (directions position).2)) ∈
      sourceSmoothRange parameters := by
  apply (quotientEta_mem_iff parameters 3 (le_refl 3) _).1
  have core := physicalMixedComposedDerivative_real_core family reference insideR zeroth genuine
    cellLength 3 (le_refl 3) order base insideS axis (fun position => directions position.rev)
  simp only [Fin.rev_rev] at core
  rw [← core]
  exact (iteratedFDeriv ℝ order
    (completedRealPhysicalMixedSlice parameters cellLength reference insideR 3 (le_refl 3))
    (realMixedCoreEmbed parameters reference insideR 9 (realHighLarge 3) base)
    (fun position => realMixedCoreEmbed parameters reference insideR 9 (realHighLarge 3)
      (directions position.rev))).property

end Grad.PhysicalCoordinates

