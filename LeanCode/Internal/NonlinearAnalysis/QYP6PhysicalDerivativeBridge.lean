import QYP5PhysicalGrades
import QY18MixedOuterCompletion

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 600000

open Filter
open scoped Topology BigOperators ContDiff

namespace Grad.PhysicalCoordinates

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.Q24Realization Grad.MixedQuotientComposition Grad.QuotientProjection
open Grad.AxisCore Grad.SmoothingFamily Grad.ConstrainedGrades

theorem physicalMixed_iteratedFDeriv_of_directional
    (parameters : PhaseParameters) (cellLength : ℝ) (reference : Grad.Constraints.Seed.Parameters)
    (grade : ℕ)
    (tower : (order : ℕ) → (Grad.Constraints.Seed.Parameters × JointState parameters) →
      (Fin order → Grad.Constraints.Seed.Parameters × JointState parameters) → QuotientRows parameters)
    (zeroth : ∀ base, mixedCoreEmbed parameters (grade + 6) base ∈ mixedDomain parameters (grade + 6) →
      ∀ directions, quotientEta parameters grade (tower 0 base directions) =
        completedPhysicalMixedSlice parameters cellLength reference grade (mixedCoreEmbed parameters (grade + 6) base))
    (step : ∀ order base (directions : Fin (order + 1) → Grad.Constraints.Seed.Parameters × JointState parameters),
      mixedCoreEmbed parameters (grade + 6) base ∈ mixedDomain parameters (grade + 6) →
      ∀ q, Tendsto (fun t : ℝ => rowsGradeNorm q
        (t⁻¹ • (tower order (base + t • directions (Fin.last order))
          (fun position => directions position.castSucc) -
          tower order base (fun position => directions position.castSucc)) -
          tower (order + 1) base directions)) (𝓝[≠] (0 : ℝ)) (𝓝 0))
    (order : ℕ) (base : Grad.Constraints.Seed.Parameters × JointState parameters)
    (inside : mixedCoreEmbed parameters (grade + 6) base ∈ mixedDomain parameters (grade + 6))
    (directions : Fin order → Grad.Constraints.Seed.Parameters × JointState parameters) :
    iteratedFDeriv ℝ order (completedPhysicalMixedSlice parameters cellLength reference grade)
      (mixedCoreEmbed parameters (grade + 6) base)
      (fun position => mixedCoreEmbed parameters (grade + 6) (directions position)) =
      quotientEta parameters grade (tower order base (fun position => directions position.rev)) := by
  apply iteratedFDeriv_core_of_directional (mixedCoreLinear parameters (grade + 6))
    (completedPhysicalMixedSlice parameters cellLength reference grade) (mixedDomain parameters (grade + 6))
    (mixedDomain_isOpen parameters (grade + 6))
    (completedPhysicalMixedSlice_contDiffOn parameters cellLength reference grade)
    (fun order base directions => quotientEta parameters grade (tower order base directions)) zeroth
  · intro count point tuple member
    exact rows_hasDerivAt_of_directional parameters grade
      (fun state => tower count state (fun position => tuple position.castSucc)) point (tuple (Fin.last count))
      (tower (count + 1) point tuple) (step count point tuple member)
  · exact inside

variable {parameters : PhaseParameters}

section ActualIdentification

variable (family : (order : ℕ) → Input parameters →
    (Fin order → Input parameters) → QuotientState parameters)
  (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
  (zeroth : ∀ (base : Input parameters) (insideS : base.1 ∈ Seed.parameterDomain),
    ChartAxisCondition base.2.2 → ∀ directions,
      family 0 base directions = physicalReferenceState parameters reference insideR base.1 insideS base.2)
  (genuine : ∀ order base (directions : Fin (order + 1) → Input parameters),
    CoreAdmissible base → IsStateDirectionalDerivative
      (fun point => family order point (fun position => directions position.castSucc))
      base (directions (Fin.last order)) (family (order + 1) base directions))

include zeroth genuine in
/-- A genuine literal inner tower gives the actual completed mixed
Fréchet derivative, through the unchanged five homogeneous quotient parts. -/
theorem physicalMixedComposedDerivative_core (cellLength : ℝ) (grade order : ℕ)
    (base : Input parameters) (admissible : CoreAdmissible base)
    (directions : Fin order → Input parameters) :
    iteratedFDeriv ℝ order (completedPhysicalMixedSlice parameters cellLength reference grade)
      (mixedCoreEmbed parameters (grade + 6) base)
      (fun position => mixedCoreEmbed parameters (grade + 6) (directions position)) =
      quotientEta parameters grade
        (composedDerivative family cellLength order base (fun position => directions position.rev)) := by
  apply physicalMixed_iteratedFDeriv_of_directional parameters cellLength reference grade
    (composedDerivative family cellLength)
  · intro point member tuple
    have actual := (CoreAdmissible_iff_domain (grade + 6) point).2 member
    rw [completedPhysicalMixedSlice_core parameters cellLength reference insideR grade point actual.1 actual.2,
      MixedQuotientComposition.composedDerivative_zeroth, zeroth point actual.1 actual.2]
    rfl
  · intro count point tuple member q
    have actual := (CoreAdmissible_iff_domain (grade + 6) point).2 member
    have step := composedDerivative_genuine family CoreAdmissible genuine cellLength count point tuple actual q
    have scalar (t : ℝ) (value : QuotientRows parameters) :
        ((t : ℂ)⁻¹) • value = t⁻¹ • value := by
      rw [← Complex.ofReal_inv, Complex.coe_smul (t⁻¹) value]
    simpa only [scalar] using step
  · exact (CoreAdmissible_iff_domain (grade + 6) base).1 admissible

end ActualIdentification

private theorem physical_continuous_fiber_majorant {B E D : Type*}
    [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace D]
    (fiber : B → E) (fiberContinuous : Continuous fiber)
    (majorant : E × D → ℝ) (majorantContinuous : Continuous majorant) (constant : ℝ) :
    Continuous (fun pair : B × D => constant * majorant (fiber pair.1, pair.2)) :=
  continuous_const.mul (majorantContinuous.comp
    ((fiberContinuous.comp continuous_fst).prodMk continuous_snd))

/-- The actual Q24 completion step for a supplied, proved mixed core
estimate. Finite seed and curvature are held fixed throughout density.
This adapter does not assert the missing Q23 core estimate. -/
theorem completedPhysicalMixedSlice_bound_of_core
    (parameters : PhaseParameters) (cellLength : ℝ) (reference : Seed.Parameters)
    (grade order : ℕ) (seedPatch : Set Seed.Parameters) (curvatureBound stateBound constant : ℝ)
    (coreBound : ∀ (base : Seed.Parameters × JointState parameters)
      (directions : Fin order → Seed.Parameters × JointState parameters),
      base.1 ∈ seedPatch → ‖base.2.1‖ ≤ curvatureBound →
      mixedCoreEmbed parameters (grade + 6) base ∈ mixedDomain parameters (grade + 6) →
      chartStateNorm 4 base.2.2 ≤ stateBound + 1 →
      ‖iteratedFDeriv ℝ order (completedPhysicalMixedSlice parameters cellLength reference grade)
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
    ‖iteratedFDeriv ℝ order (completedPhysicalMixedSlice parameters cellLength reference grade) base directions‖ ≤
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
    physical_continuous_fiber_majorant (B := XAmbient parameters (grade + 6))
      (E := MixedAmbient parameters (grade + 6))
      (D := Fin order → MixedAmbient parameters (grade + 6))
      fiber fiberContinuous
      (fun pair => mixedCompletedOneHigh parameters grade order pair.1 pair.2)
      (mixedCompletedOneHigh_continuous parameters grade order) constant
  have identity : fiber (mixedStatePart parameters (grade + 6) base) = base :=
    mixedStateFiber_reconstruct parameters (grade + 6) base
  suffices estimate : ‖iteratedFDeriv ℝ order (completedPhysicalMixedSlice parameters cellLength reference grade)
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
    fiber fiberContinuous (completedPhysicalMixedSlice parameters cellLength reference grade)
    (mixedDomain parameters (grade + 6)) (mixedDomain_isOpen parameters (grade + 6))
    (completedPhysicalMixedSlice_contDiffOn parameters cellLength reference grade) order
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

theorem physicalMixedComposedDerivative_core_bound
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
    (Admissible : Input parameters → Prop)
    (coreAdmissible : ∀ base, Admissible base → CoreAdmissible base)
    (innerBound : ∀ (grade count : ℕ), ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : Input parameters) (tuple : Fin count → Input parameters),
        Admissible base →
        stateNorm grade (family count base tuple) ≤ constant * inputOneHigh grade 4 base tuple)
    (cellLength : ℝ) (grade order : ℕ) (ball : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : Input parameters) (directions : Fin order → Input parameters),
        Admissible base → baseNorm 4 base ≤ ball →
        ‖iteratedFDeriv ℝ order (completedPhysicalMixedSlice parameters cellLength reference grade)
          (mixedCoreEmbed parameters (grade + 6) base)
          (fun position => mixedCoreEmbed parameters (grade + 6) (directions position))‖ ≤
          constant * mixedCompletedOneHigh parameters grade order
            (mixedCoreEmbed parameters (grade + 6) base)
            (fun position => mixedCoreEmbed parameters (grade + 6) (directions position)) := by
  obtain ⟨constant, nonneg, estimate⟩ :=
    composedDerivative_bound family Admissible innerBound cellLength grade order ball
  refine ⟨2 * constant, by positivity, fun base directions admissible bounded => ?_⟩
  rw [physicalMixedComposedDerivative_core family reference insideR zeroth genuine cellLength grade order
    base (coreAdmissible base admissible)]
  calc
    _ ≤ 2 * rowsGradeNorm grade
        (composedDerivative family cellLength order base (fun position => directions position.rev)) :=
      quotientEta_norm_le_rows parameters grade _
    _ ≤ 2 * (constant * inputOneHigh (grade + 6) 4 base (fun position => directions position.rev)) :=
      mul_le_mul_of_nonneg_left
        (estimate base (fun position => directions position.rev) admissible bounded) (by norm_num)
    _ = _ := by
      have reindex := inputOneHigh_reindex (grade + 6) 4 base directions Fin.revPerm
      change inputOneHigh (grade + 6) 4 base (fun position => directions position.rev) = _ at reindex
      rw [reindex, inputOneHigh_completed]
      ring

theorem physicalMixedComposedDerivative_bound_on_patch
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
    (seedPatch : Set Seed.Parameters) (curvatureBound stateBound : ℝ)
    (innerBound : ∀ (grade count : ℕ), ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : Input parameters) (tuple : Fin count → Input parameters),
        base.1 ∈ seedPatch → ‖base.2.1‖ ≤ curvatureBound → CoreAdmissible base →
        baseNorm 4 base ≤ stateBound + 1 →
        stateNorm grade (family count base tuple) ≤ constant * inputOneHigh grade 4 base tuple)
    (cellLength : ℝ) (grade order : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : MixedAmbient parameters (grade + 6))
        (directions : Fin order → MixedAmbient parameters (grade + 6)),
        mixedSeed parameters (grade + 6) base ∈ seedPatch →
        ‖(mixedJoint parameters (grade + 6) base).ofLp.1‖ ≤ curvatureBound →
        base ∈ mixedDomain parameters (grade + 6) →
        ‖xLowering parameters (realLowLeHigh grade) (mixedStatePart parameters (grade + 6) base)‖ ≤ stateBound →
        ‖iteratedFDeriv ℝ order (completedPhysicalMixedSlice parameters cellLength reference grade) base directions‖ ≤
          constant * mixedCompletedOneHigh parameters grade order base directions := by
  let Admissible : Input parameters → Prop := fun base =>
    base.1 ∈ seedPatch ∧ ‖base.2.1‖ ≤ curvatureBound ∧ CoreAdmissible base ∧
      baseNorm 4 base ≤ stateBound + 1
  have coreAdmissible : ∀ base, Admissible base → CoreAdmissible base := fun _ member => member.2.2.1
  have inner : ∀ (q count : ℕ), ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : Input parameters) (tuple : Fin count → Input parameters), Admissible base →
        stateNorm q (family count base tuple) ≤ constant * inputOneHigh q 4 base tuple := by
    intro q count
    obtain ⟨constant, nonneg, bound⟩ := innerBound q count
    exact ⟨constant, nonneg, fun base tuple member =>
      bound base tuple member.1 member.2.1 member.2.2.1 member.2.2.2⟩
  obtain ⟨constant, nonneg, bound⟩ := physicalMixedComposedDerivative_core_bound
    family reference insideR zeroth genuine Admissible coreAdmissible inner cellLength grade order (stateBound + 1)
  refine ⟨constant, nonneg, fun base directions inPatch curvature inside bounded => ?_⟩
  apply completedPhysicalMixedSlice_bound_of_core parameters cellLength reference grade order
    seedPatch curvatureBound stateBound constant _ base directions inPatch curvature inside bounded
  intro point tuple inPatch curvature inside bounded
  exact bound point tuple
    ⟨inPatch, curvature, (CoreAdmissible_iff_domain (grade + 6) point).2 inside, bounded⟩ bounded

end Grad.PhysicalCoordinates
