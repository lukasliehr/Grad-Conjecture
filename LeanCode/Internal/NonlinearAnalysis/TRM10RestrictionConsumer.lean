import TRM9LiteralFourierShift

noncomputable section

namespace Grad.SourceCollarAngular

open Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.ClosedJets Grad.CartesianState

/-- The actual annular radial component of an arbitrary completed original
field.  No derivatives or angular weight are lost. -/
def completedRadialContraction (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ) :
    AGrade parameters 2 (power + radial) →L[ℂ]
      annularDerivativeGraph 1 lower positive radial :=
  (annularRadialContraction lower positive power).comp
    (completedRestriction lower positive bounded parameters power radial)

/-- The actual annular tangential component of an arbitrary completed
original field, with the same `ν^power` and radial graph order. -/
def completedTangentialContraction (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ) :
    AGrade parameters 2 (power + radial) →L[ℂ]
      annularDerivativeGraph 1 lower positive radial :=
  (annularTangentialContraction lower positive power).comp
    (completedRestriction lower positive bounded parameters power radial)

theorem completedRadialContraction_bound (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (parameters : PhaseParameters) (power radial : ℕ)
    (field : AGrade parameters 2 (power + radial)) :
    ‖completedRadialContraction lower positive bounded parameters power radial field‖ ≤
      (2 * (2 : ℝ) ^ power * restrictionGraphConstant power radial) * ‖field‖ := by
  calc
    _ ≤ 2 * (2 : ℝ) ^ power *
        ‖completedRestriction lower positive bounded parameters power radial field‖ :=
      annularRadialContraction_apply_norm_le lower positive power _
    _ ≤ 2 * (2 : ℝ) ^ power *
        (restrictionGraphConstant power radial * ‖field‖) := by
      gcongr
      exact completedRestriction_bound lower positive bounded parameters power radial field
    _ = _ := by ring

theorem completedTangentialContraction_bound (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (parameters : PhaseParameters) (power radial : ℕ)
    (field : AGrade parameters 2 (power + radial)) :
    ‖completedTangentialContraction lower positive bounded parameters power radial field‖ ≤
      (2 * (2 : ℝ) ^ power * restrictionGraphConstant power radial) * ‖field‖ := by
  calc
    _ ≤ 2 * (2 : ℝ) ^ power *
        ‖completedRestriction lower positive bounded parameters power radial field‖ :=
      annularTangentialContraction_apply_norm_le lower positive power _
    _ ≤ 2 * (2 : ℝ) ^ power *
        (restrictionGraphConstant power radial * ‖field‖) := by
      gcongr
      exact completedRestriction_bound lower positive bounded parameters power radial field
    _ = _ := by ring

theorem completedRadialContraction_core
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ)
    (field : GradeCore parameters 2 (power + radial))
    (index : Fin (radial + 1)) (mode : ℤ × ℤ) :
    (completedRadialContraction lower positive bounded parameters power radial
      (aGradeEta parameters field)).val index mode =
      (annularRadialContraction lower positive power
        (completedRestriction lower positive bounded parameters power radial
          (aGradeEta parameters field))).val index mode := rfl

theorem completedTangentialContraction_core
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ)
    (field : GradeCore parameters 2 (power + radial))
    (index : Fin (radial + 1)) (mode : ℤ × ℤ) :
    (completedTangentialContraction lower positive bounded parameters power radial
      (aGradeEta parameters field)).val index mode =
      (annularTangentialContraction lower positive power
        (completedRestriction lower positive bounded parameters power radial
          (aGradeEta parameters field))).val index mode := rfl

/-- Exact BS36-ready `F₀=e_θ·f` and `F₁=e_r·f` restriction at
angular order `t+1`, including both value and weak radial derivative. -/
theorem forcePolarComponentsConsumer (tangential : ℕ) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
        (parameters : PhaseParameters) (field : AGrade parameters 2 (tangential + 2)),
        ‖completedTangentialContraction lower positive bounded parameters
            (tangential + 1) 1 field‖ ≤ constant * ‖field‖ ∧
        ‖completedRadialContraction lower positive bounded parameters
            (tangential + 1) 1 field‖ ≤ constant * ‖field‖ := by
  have totalNonneg : 0 ≤ 2 * (2 : ℝ) ^ (tangential + 1) *
      restrictionGraphConstant (tangential + 1) 1 := by
    exact mul_nonneg (by positivity)
      (restrictionGraphConstant_nonnegative (tangential + 1) 1)
  refine ⟨1 + 2 * (2 : ℝ) ^ (tangential + 1) *
      restrictionGraphConstant (tangential + 1) 1, ?_, ?_⟩
  · linarith
  · intro lower positive bounded parameters field
    constructor
    · exact (completedTangentialContraction_bound lower positive bounded parameters
        (tangential + 1) 1 field).trans (by
          exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
    · exact (completedRadialContraction_bound lower positive bounded parameters
        (tangential + 1) 1 field).trans (by
          exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

/-- Exact lower-order `F₂` restriction carrier required alongside the two
polar contractions: `p=t`, `k=1`, hence only original grade `t+1`. -/
theorem fourthPolarRestrictionConsumer (tangential : ℕ) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
        (parameters : PhaseParameters) (field : AGrade parameters 1 (tangential + 1)),
        ‖completedRestriction lower positive bounded parameters tangential 1 field‖ ≤
          constant * ‖field‖ := by
  have constantNonneg := restrictionGraphConstant_nonnegative tangential 1
  refine ⟨1 + restrictionGraphConstant tangential 1, by linarith, ?_⟩
  intro lower positive bounded parameters field
  exact (completedRestriction_bound lower positive bounded parameters tangential 1 field).trans (by
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

end Grad.SourceCollarAngular
