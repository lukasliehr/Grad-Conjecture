import RSC8RestrictedGraph

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.SourceCollarRestriction
open Grad.SourceCollarDivision Grad.ClosedJets Grad.CartesianState Grad.CompatibleCompletion

/-- Literal polar restriction, extended from the original dense smooth core.
The target retains the actual radial weak derivative identities and r dr norm. -/
def completedRestriction {dimension : ℕ} (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ) :
    AGrade parameters dimension (power + radial) →L[ℂ]
      annularDerivativeGraph dimension lower positive radial :=
  (completedRestrictionArray lower positive bounded parameters power radial).codRestrict
    (annularDerivativeGraph dimension lower positive radial)
    (completedRestrictionArray_graph lower positive bounded parameters power radial)

theorem completedRestriction_bound {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ)
    (field : AGrade parameters dimension (power + radial)) :
    ‖completedRestriction lower positive bounded parameters power radial field‖ ≤
      restrictionGraphConstant power radial * ‖field‖ :=
  completedRestrictionArray_bound lower positive bounded parameters power radial field

theorem completedRestriction_core {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ)
    (field : GradeCore parameters dimension (power + radial)) (index : Fin (radial + 1)) (mode : ℤ × ℤ) :
    (completedRestriction lower positive bounded parameters power radial (aGradeEta parameters field)).val index mode =
      restrictionModeLp lower power index.val parameters field.toCore mode := by
  change completedRestrictionRow (power := power) (radial := index.val)
    lower positive bounded parameters (by omega) (aGradeEta parameters field) mode = _
  rw [completedRestrictionRow_core]
  rfl

/-- Exact bounded dense-core extension is unique, also at grades zero, one and two.
No point evaluation of an arbitrary L2 field is used. -/
theorem completedRestriction_unique {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ)
    (other : AGrade parameters dimension (power + radial) →L[ℂ]
      annularDerivativeGraph dimension lower positive radial)
    (coreLaw : ∀ (field : GradeCore parameters dimension (power + radial))
      (index : Fin (radial + 1)) (mode : ℤ × ℤ),
      (other (aGradeEta parameters field)).val index mode =
        restrictionModeLp lower power index.val parameters field.toCore mode) :
    other = completedRestriction lower positive bounded parameters power radial := by
  apply denseCoreContinuousLinearMap_ext parameters
  intro core
  apply Subtype.ext
  apply PiLp.ext
  intro index
  apply Subtype.ext
  funext mode
  exact (coreLaw core index mode).trans (completedRestriction_core lower positive bounded parameters power radial core index mode).symm

/-- Every radial row agrees across original grade inclusions. In particular
the zeroth row is the same canonical L2 restriction at all available grades. -/
theorem completedRestrictionRow_inclusion {dimension low high power radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (paid : power + radial ≤ low) (grades : low ≤ high) :
    (completedRestrictionRow (dimension := dimension) (power := power) (radial := radial) lower positive bounded parameters paid).comp
        (completedInclusion parameters grades) =
      completedRestrictionRow (power := power) (radial := radial) lower positive bounded parameters (paid.trans grades) := by
  apply denseCoreContinuousLinearMap_ext parameters
  intro core
  rw [ContinuousLinearMap.comp_apply, completedInclusion_apply_eta, completedRestrictionRow_core,
    completedRestrictionRow_core]
  rfl

theorem completedRestriction_norm {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ)
    (field : AGrade parameters dimension (power + radial)) :
    ‖completedRestriction lower positive bounded parameters power radial field‖ =
      ∑ index : Fin (radial + 1), ‖(completedRestriction lower positive bounded parameters power radial field).val index‖ :=
  completedRestrictionArray_norm lower positive bounded parameters power radial field

end Grad.SourceCollarRestriction
