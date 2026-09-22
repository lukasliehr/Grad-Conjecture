import TRM10RestrictionConsumer

noncomputable section

namespace Grad.SourceCollarAngular

open Grad.SourceCollarDivision

/-- Exact dependency-ready fixed polar multiplier boundary.  Every operator
acts on the same `ν^power` Fourier row and the same full weak radial graph;
the constants are uniform in the annulus radius. -/
def PolarAngularMultiplierGoal : Prop :=
  (∀ (dimension radial power : ℕ) (lower : ℝ) (positive : 0 < lower)
      (field : annularDerivativeGraph dimension lower positive radial)
      (index : Fin (radial + 1)) (mode : ℤ × ℤ),
      (annularGraphShift lower positive power 1 field).val index mode =
        annularShiftScalar power 1 mode • field.val index (mode.1 - 1, mode.2) ∧
      ‖annularCosine lower positive power field‖ ≤ (2 : ℝ) ^ power * ‖field‖ ∧
      ‖annularSine lower positive power field‖ ≤ (2 : ℝ) ^ power * ‖field‖) ∧
  (∀ (radial power : ℕ) (lower : ℝ) (positive : 0 < lower)
      (field : annularDerivativeGraph 2 lower positive radial),
      ‖annularRadialContraction lower positive power field‖ ≤
        2 * (2 : ℝ) ^ power * ‖field‖ ∧
      ‖annularTangentialContraction lower positive power field‖ ≤
        2 * (2 : ℝ) ^ power * ‖field‖)

theorem actualPolarAngularMultipliers : PolarAngularMultiplierGoal := by
  constructor
  · intro dimension radial power lower positive field index mode
    exact ⟨annularGraphShift_apply lower positive power 1 field index mode,
      annularCosine_apply_norm_le lower positive power field,
      annularSine_apply_norm_le lower positive power field⟩
  · intro radial power lower positive field
    exact ⟨annularRadialContraction_apply_norm_le lower positive power field,
      annularTangentialContraction_apply_norm_le lower positive power field⟩

/-- Immediate exact downstream interface: the BS36 polar force components
use `p=t+1,k=1`, while its lower-order fourth component uses `p=t,k=1`. -/
theorem polarBulkRestrictionBoundary (tangential : ℕ) :
    (∃ constant : ℝ, 0 < constant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
        (parameters : Grad.CartesianState.PhaseParameters)
        (field : Grad.CartesianState.AGrade parameters 2 (tangential + 2)),
        ‖completedTangentialContraction lower positive bounded parameters
            (tangential + 1) 1 field‖ ≤ constant * ‖field‖ ∧
        ‖completedRadialContraction lower positive bounded parameters
            (tangential + 1) 1 field‖ ≤ constant * ‖field‖) ∧
    (∃ constant : ℝ, 0 < constant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
        (parameters : Grad.CartesianState.PhaseParameters)
        (field : Grad.CartesianState.AGrade parameters 1 (tangential + 1)),
        ‖Grad.SourceCollarRestriction.completedRestriction lower positive bounded parameters
            tangential 1 field‖ ≤ constant * ‖field‖) :=
  ⟨forcePolarComponentsConsumer tangential, fourthPolarRestrictionConsumer tangential⟩

end Grad.SourceCollarAngular
