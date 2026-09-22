import Q24DirectionalBridge

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

open scoped BigOperators ContDiff

namespace Grad.Q24Realization

open Grad.CartesianState Grad.NonlinearQuotientBounds Grad.Constraints Grad.QuotientProjection

theorem completedFixedSlice_derivative_core (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade order : ℕ)
    (base : JointState parameters) (axis : ChartAxisCondition base.2)
    (directions : Fin order → JointState parameters) :
    iteratedFDeriv ℝ order
      (completedFixedSlice parameters cellLength reference insideR seed insideS grade)
      (jointCoreEmbed parameters (grade + 6) base)
      (fun position => jointCoreEmbed parameters (grade + 6) (directions position)) =
      quotientEta parameters grade
        (fixedSliceDerivative parameters cellLength reference insideR seed insideS order base
          (fun position => directions position.rev)) := by
  apply iteratedFDeriv_core_of_directional
    ((jointCoreLinear parameters (grade + 6)).restrictScalars ℝ)
    (completedFixedSlice parameters cellLength reference insideR seed insideS grade)
    (jointDomain parameters (grade + 6)) (jointDomain_isOpen parameters (grade + 6))
    (completedFixedSlice_contDiffOn parameters cellLength reference insideR seed insideS grade)
    (fun order base directions => quotientEta parameters grade
      (fixedSliceDerivative parameters cellLength reference insideR seed insideS order base directions))
  · intro point inside directions
    change quotientEta parameters grade
      (fixedSliceDerivative parameters cellLength reference insideR seed insideS 0 point directions) =
      completedFixedSlice parameters cellLength reference insideR seed insideS grade
        (jointCoreEmbed parameters (grade + 6) point)
    rw [completedFixedSlice_core parameters cellLength reference insideR seed insideS grade point
      ((jointDomain_core_iff parameters (grade + 6) point).1 inside)]
    congr 1
    unfold fixedSliceDerivative
    rw [composedDerivative_zeroth, referenceFamily_zeroth]
    rfl
  · intro count point directions inside
    have genuine := composedDerivative_genuine (referenceFamily parameters reference insideR seed insideS)
      (fun state => ChartAxisCondition state.2)
      (fun order base directions admissible =>
        referenceFamily_genuine reference insideR seed insideS order base directions admissible)
      cellLength count point directions ((jointDomain_core_iff parameters (grade + 6) point).1 inside)
    exact coreRows_hasDerivAt parameters grade
      (fun state => fixedSliceDerivative parameters cellLength reference insideR seed insideS count state
        (fun position => directions position.castSucc)) point (directions (Fin.last count))
      (fixedSliceDerivative parameters cellLength reference insideR seed insideS (count + 1) point directions) genuine
  · exact (jointDomain_core_iff parameters (grade + 6) base).2 axis

theorem oneHigh_sum_reindex {arity : ℕ} (permutation : Equiv.Perm (Fin arity))
    (high low : Fin arity → ℝ) :
    (∑ position, high (permutation position) *
      ∏ other ∈ Finset.univ.erase position, low (permutation other)) =
    ∑ position, high position * ∏ other ∈ Finset.univ.erase position, low other := by
  classical
  have full : Finset.univ.map permutation.toEmbedding = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro position
    exact Finset.mem_map.2 ⟨permutation.symm position, Finset.mem_univ _, permutation.apply_symm_apply position⟩
  have factor (position : Fin arity) :
      (∏ other ∈ Finset.univ.erase position, low (permutation other)) =
        ∏ other ∈ Finset.univ.erase (permutation position), low other := by
    have equality := Finset.prod_map (Finset.univ.erase position) permutation.toEmbedding low
    rw [Finset.map_erase, full] at equality
    exact equality.symm
  simp only [factor]
  exact Equiv.sum_comp permutation (fun position => high position *
    ∏ other ∈ Finset.univ.erase position, low other)

theorem completedFixedSlice_derivative_core_bound (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade order : ℕ) (bound : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : JointState parameters) (directions : Fin order → JointState parameters),
        ChartAxisCondition base.2 → jointNorm 4 base ≤ bound →
        ‖iteratedFDeriv ℝ order
          (completedFixedSlice parameters cellLength reference insideR seed insideS grade)
          (jointCoreEmbed parameters (grade + 6) base)
          (fun position => jointCoreEmbed parameters (grade + 6) (directions position))‖ ≤
        constant * ((1 + jointNorm (grade + 6) base) *
          ∏ position, jointNorm 4 (directions position) +
          ∑ position, jointNorm (grade + 6) (directions position) *
            ∏ other ∈ Finset.univ.erase position, jointNorm 4 (directions other)) := by
  obtain ⟨constant, nonneg, estimate⟩ :=
    composedDerivative_bound (referenceFamily parameters reference insideR seed insideS)
      (fun state => ChartAxisCondition state.2)
      (fun grade count => referenceFamily_bound reference insideR seed insideS grade count)
      cellLength grade order bound
  refine ⟨2 * constant, by positivity, fun base directions axis bounded => ?_⟩
  rw [completedFixedSlice_derivative_core parameters cellLength reference insideR seed insideS grade order base axis]
  apply (quotientEta_norm_le_rows parameters grade _).trans
  have estimate := mul_le_mul_of_nonneg_left
    (estimate base (fun position => directions position.rev) axis bounded) (by norm_num : (0 : ℝ) ≤ 2)
  change 2 * rowsGradeNorm grade
    (fixedSliceDerivative parameters cellLength reference insideR seed insideS order base
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

end Grad.Q24Realization
