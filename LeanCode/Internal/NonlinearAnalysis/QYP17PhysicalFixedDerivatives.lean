import QYP16PhysicalFixedAmbient

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

open scoped BigOperators ContDiff

namespace Grad.PhysicalCoordinates

open Grad.CartesianState Grad.NonlinearQuotientBounds Grad.Constraints Grad.QuotientProjection
open Grad.Q24Realization

theorem completedPhysicalFixedSlice_derivative_core (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade order : ℕ)
    (base : JointState parameters) (axis : ChartAxisCondition base.2)
    (directions : Fin order → JointState parameters) :
    iteratedFDeriv ℝ order
      (completedPhysicalFixedSlice parameters cellLength reference insideR seed insideS grade)
      (jointCoreEmbed parameters (grade + 6) base)
      (fun position => jointCoreEmbed parameters (grade + 6) (directions position)) =
      quotientEta parameters grade
        (physicalFixedSliceDerivative parameters cellLength reference insideR seed insideS order base
          (fun position => directions position.rev)) := by
  apply iteratedFDeriv_core_of_directional
    ((jointCoreLinear parameters (grade + 6)).restrictScalars ℝ)
    (completedPhysicalFixedSlice parameters cellLength reference insideR seed insideS grade)
    (jointDomain parameters (grade + 6)) (jointDomain_isOpen parameters (grade + 6))
    (completedPhysicalFixedSlice_contDiffOn parameters cellLength reference insideR seed insideS grade)
    (fun order base directions => quotientEta parameters grade
      (physicalFixedSliceDerivative parameters cellLength reference insideR seed insideS order base directions))
  · intro point inside directions
    change quotientEta parameters grade
      (physicalFixedSliceDerivative parameters cellLength reference insideR seed insideS 0 point directions) =
      completedPhysicalFixedSlice parameters cellLength reference insideR seed insideS grade
        (jointCoreEmbed parameters (grade + 6) point)
    rw [completedPhysicalFixedSlice_core parameters cellLength reference insideR seed insideS grade point
      ((jointDomain_core_iff parameters (grade + 6) point).1 inside)]
    congr 1
    unfold physicalFixedSliceDerivative
    rw [composedDerivative_zeroth, physicalFixedReferenceFamily_zero]
    rfl
  · intro count point directions inside
    have genuine := composedDerivative_genuine (physicalFixedReferenceFamily parameters reference insideR seed insideS)
      (fun state => ChartAxisCondition state.2)
      (fun order base directions admissible =>
        physicalFixedReferenceFamily_genuine reference insideR seed insideS order base directions admissible)
      cellLength count point directions ((jointDomain_core_iff parameters (grade + 6) point).1 inside)
    exact coreRows_hasDerivAt parameters grade
      (fun state => physicalFixedSliceDerivative parameters cellLength reference insideR seed insideS count state
        (fun position => directions position.castSucc)) point (directions (Fin.last count))
      (physicalFixedSliceDerivative parameters cellLength reference insideR seed insideS (count + 1) point directions) genuine
  · exact (jointDomain_core_iff parameters (grade + 6) base).2 axis

theorem completedPhysicalFixedSlice_derivative_core_bound (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade order : ℕ) (bound : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : JointState parameters) (directions : Fin order → JointState parameters),
        ChartAxisCondition base.2 → jointNorm 4 base ≤ bound →
        ‖iteratedFDeriv ℝ order
          (completedPhysicalFixedSlice parameters cellLength reference insideR seed insideS grade)
          (jointCoreEmbed parameters (grade + 6) base)
          (fun position => jointCoreEmbed parameters (grade + 6) (directions position))‖ ≤
        constant * ((1 + jointNorm (grade + 6) base) *
          ∏ position, jointNorm 4 (directions position) +
          ∑ position, jointNorm (grade + 6) (directions position) *
            ∏ other ∈ Finset.univ.erase position, jointNorm 4 (directions other)) := by
  obtain ⟨constant, nonneg, estimate⟩ :=
    composedDerivative_bound (physicalFixedReferenceFamily parameters reference insideR seed insideS)
      (fun state => ChartAxisCondition state.2)
      (fun grade count => physicalFixedReferenceFamily_bound reference insideR seed insideS grade count)
      cellLength grade order bound
  refine ⟨2 * constant, by positivity, fun base directions axis bounded => ?_⟩
  rw [completedPhysicalFixedSlice_derivative_core parameters cellLength reference insideR seed insideS grade order base axis]
  apply (quotientEta_norm_le_rows parameters grade _).trans
  have estimate := mul_le_mul_of_nonneg_left
    (estimate base (fun position => directions position.rev) axis bounded) (by norm_num : (0 : ℝ) ≤ 2)
  change 2 * rowsGradeNorm grade
    (physicalFixedSliceDerivative parameters cellLength reference insideR seed insideS order base
      (fun position => directions position.rev)) ≤ _ at estimate
  have productEquality := Equiv.prod_comp Fin.revPerm (fun position => jointNorm 4 (directions position))
  have sumEquality := oneHigh_sum_reindex Fin.revPerm
    (fun position => jointNorm (grade + 6) (directions position))
    (fun position => jointNorm 4 (directions position))
  unfold jointOneHigh at estimate
  change (∏ position : Fin order, jointNorm 4 (directions position.rev)) = _ at productEquality
  change (∑ position : Fin order, jointNorm (grade + 6) (directions position.rev) *
    ∏ other ∈ Finset.univ.erase position, jointNorm 4 (directions other.rev)) = _ at sumEquality
  rw [productEquality, sumEquality] at estimate
  exact estimate.trans_eq (by ring)

end Grad.PhysicalCoordinates

