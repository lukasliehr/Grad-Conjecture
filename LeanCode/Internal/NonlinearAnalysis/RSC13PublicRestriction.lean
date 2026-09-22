import RSC12PhysicalRealization

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.SourceCollarRestriction
open Grad.SourceCollarDivision Grad.ClosedJets Grad.CartesianState

/-- Literal smooth polar derivative/Fourier law fixing the completed operator. -/
def RestrictionCoreLaw {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (parameters : PhaseParameters) (power radial : ℕ)
    (restriction : AGrade parameters dimension (power + radial) →L[ℂ]
      annularDerivativeGraph dimension lower positive radial) : Prop :=
  ∀ (field : GradeCore parameters dimension (power + radial))
    (index : Fin (radial + 1)) (mode : ℤ × ℤ),
    (restriction (aGradeEta parameters field)).val index mode =
      restrictionModeLp lower power index.val parameters field.toCore mode

/-- Exact BS34 nonsingular restriction: p+k source derivatives, all integer
grades, unchanged original weights, sum of radial L2(r dr) norms, uniform a.
At low grades it is the unique bounded extension of literal smooth restriction;
RSC12 additionally identifies actual continuous representatives wherever they exist. -/
def NonsingularRestrictionGoal : Prop :=
  ∀ power radial : ℕ, ∃ constant : ℝ, 0 < constant ∧
    ∀ (dimension : ℕ) (parameters : PhaseParameters) (lower : ℝ)
      (positive : 0 < lower), lower ≤ 1 / 2 →
      ∃ restriction : AGrade parameters dimension (power + radial) →L[ℂ]
          annularDerivativeGraph dimension lower positive radial,
        RestrictionCoreLaw lower positive parameters power radial restriction ∧
        (∀ field, ‖restriction field‖ ≤ constant * ‖field‖) ∧
        (∀ other, RestrictionCoreLaw lower positive parameters power radial other → other = restriction)

theorem actualNonsingularRestriction : NonsingularRestrictionGoal := by
  intro power radial
  refine ⟨restrictionGraphConstant power radial + 1,
    by linarith [restrictionGraphConstant_nonnegative power radial], ?_⟩
  intro dimension parameters lower positive half
  have bounded : lower ≤ 1 := half.trans (by norm_num)
  refine ⟨completedRestriction lower positive bounded parameters power radial,
    completedRestriction_core lower positive bounded parameters power radial, ?_, ?_⟩
  · intro field
    exact (completedRestriction_bound lower positive bounded parameters power radial field).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  · intro other coreLaw
    exact completedRestriction_unique lower positive bounded parameters power radial other coreLaw

/-- The actual graph has no independent derivative coordinate: equality of
the zeroth radial row determines the whole restricted source. -/
theorem restriction_graph_faithful {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (radial : ℕ) :
    Function.Injective (annularValue dimension lower positive radial) :=
  annularValue_injective dimension lower positive radial

theorem restriction_physical_norm {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ)
    (field : AGrade parameters dimension (power + radial)) :
    ‖completedRestriction lower positive bounded parameters power radial field‖ =
      ∑ index : Fin (radial + 1), Real.sqrt (∑' mode : ℤ × ℤ,
        ∫ radius in lower..1, radius *
          ‖radialValue lower ((completedRestriction lower positive bounded parameters power radial field).val index mode) radius‖ ^ 2) :=
  annularDerivativeGraph_norm lower positive bounded _

/-- The stronger F0 precursor keeps the actual first radial derivative.
Its contraction with e_theta is the separate TRM consumer, not assumed here. -/
theorem sourceForceRestrictionConsumer :
    ∀ order : ℕ, ∃ constant : ℝ, 0 < constant ∧
      ∀ (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower), lower ≤ 1 / 2 →
        ∃ restriction : AGrade parameters 2 (order + 2) →L[ℂ]
            annularDerivativeGraph 2 lower positive 1,
          (∀ (field : GradeCore parameters 2 (order + 2)) (index : Fin 2) (mode : ℤ × ℤ),
            (restriction (aGradeEta parameters field)).val index mode =
              restrictionModeLp lower (order + 1) index.val parameters field.toCore mode) ∧
          (∀ field, ‖restriction field‖ ≤ constant * ‖field‖) := by
  intro order
  obtain ⟨constant, constantPositive, result⟩ := actualNonsingularRestriction (order + 1) 1
  refine ⟨constant, constantPositive, ?_⟩
  intro parameters lower positive half
  obtain ⟨restriction, coreLaw, bound, _unique⟩ := result 2 parameters lower positive half
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using restriction
  · simpa only [RestrictionCoreLaw, Nat.add_assoc, Nat.reduceAdd] using coreLaw
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using bound

/-- The F2 precursor has exactly order+1 source regularity. -/
theorem sourceFourthRestrictionConsumer :
    ∀ order : ℕ, ∃ constant : ℝ, 0 < constant ∧
      ∀ (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower), lower ≤ 1 / 2 →
        ∃ restriction : AGrade parameters 1 (order + 1) →L[ℂ]
            annularDerivativeGraph 1 lower positive 0,
          RestrictionCoreLaw lower positive parameters (order + 1) 0 restriction ∧
          (∀ field, ‖restriction field‖ ≤ constant * ‖field‖) := by
  intro order
  obtain ⟨constant, constantPositive, result⟩ := actualNonsingularRestriction (order + 1) 0
  refine ⟨constant, constantPositive, ?_⟩
  intro parameters lower positive half
  obtain ⟨restriction, coreLaw, bound, _unique⟩ := result 1 parameters lower positive half
  exact ⟨restriction, coreLaw, bound⟩

end Grad.SourceCollarRestriction
