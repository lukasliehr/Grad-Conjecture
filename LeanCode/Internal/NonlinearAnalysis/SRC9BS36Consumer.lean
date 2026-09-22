import SRC8LiteralS11

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Grad.SourceCollarBulk

open Grad.CartesianState Grad.AxisCore
open Grad.SourceCollarDivision Grad.SourceCollarRestriction

/-- Exact sum-of-radial-`L2(r dr)` norm formulas for the three literal AH
graphs used by BS36.  The two `Fin 2` rows are respectively the weighted
value and the genuine weak radial derivative. -/
theorem completedSourceLiteralGraphNorms
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (L : ℝ) (tangential : ℕ)
    (source : ZAmbient parameters (tangential + 2)) :
    ‖completedForceS11 lower positive bounded parameters tangential source‖ =
        ∑ index : Fin 2, Real.sqrt (∑' mode : ℤ × ℤ,
          ∫ radius in lower..1, radius *
            ‖radialValue lower
              ((completedForceS11 lower positive bounded parameters tangential source).val
                index mode) radius‖ ^ 2) ∧
      ‖completedForceAngular lower positive bounded parameters tangential source‖ =
        ∑ index : Fin 2, Real.sqrt (∑' mode : ℤ × ℤ,
          ∫ radius in lower..1, radius *
            ‖radialValue lower
              ((completedForceAngular lower positive bounded parameters tangential source).val
                index mode) radius‖ ^ 2) ∧
      ‖completedFourthSource lower positive bounded parameters L tangential source‖ =
        ∑ index : Fin 2, Real.sqrt (∑' mode : ℤ × ℤ,
          ∫ radius in lower..1, radius *
            ‖radialValue lower
              ((completedFourthSource lower positive bounded parameters L tangential source).val
                index mode) radius‖ ^ 2) := by
  exact ⟨annularDerivativeGraph_norm lower positive bounded _,
    annularDerivativeGraph_norm lower positive bounded _,
    annularDerivativeGraph_norm lower positive bounded _⟩

/-- Final exact BS36 source bulk bound.  `completedForceS11` is the original
AH `S^(1;1)` coordinate `(1+|m|)nu^t W F0`; the separately retained
`completedForceAngular` is `im nu^t W F0`, with its genuine weak radial row.
The fourth component is `nu^t W(h/L)` with its weak radial row.  `F1` is also
retained in the stronger `p=t+1,k=1` graph for the subsequent literal bulk
conversion. -/
theorem actualBS36SourceBulk
    (parameters : PhaseParameters) (L : ℝ) (LPositive : 0 < L)
    (tangential : ℕ) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
        (source : ZAmbient parameters (tangential + 2)),
        ‖completedForceS11 lower positive bounded parameters tangential source‖ ≤
            constant * ‖source‖ ∧
          ‖completedForceAngular lower positive bounded parameters tangential source‖ ≤
            constant * ‖source‖ ∧
          ‖completedForceRadial lower positive bounded parameters tangential source‖ ≤
            constant * ‖source‖ ∧
          ‖completedFourthSource lower positive bounded parameters L tangential source‖ ≤
            constant * ‖source‖ := by
  refine ⟨sourceBulkConstant L tangential,
    sourceBulkConstant_positive L LPositive tangential, ?_⟩
  intro lower positive bounded source
  have total := completedSourceBulk_bound lower positive bounded parameters L LPositive
    tangential source
  have literal := completedForceS11_bound lower positive bounded parameters tangential source
  have planarConstantBound :
      planarBulkConstant tangential * ‖source‖ ≤
        sourceBulkConstant L tangential * ‖source‖ := by
    have planarNonnegative := planarBulkConstant_nonnegative tangential
    have restrictionNonnegative := restrictionGraphConstant_nonnegative tangential 1
    have inverseNonnegative : 0 ≤ L⁻¹ := inv_nonneg.mpr LPositive.le
    have sourceNonnegative : 0 ≤ ‖source‖ := norm_nonneg _
    unfold sourceBulkConstant
    nlinarith [mul_nonneg inverseNonnegative restrictionNonnegative]
  refine ⟨literal.trans planarConstantBound, ?_⟩
  have forceNonnegative := norm_nonneg
    (completedForceTangential lower positive bounded parameters tangential source)
  have angularNonnegative := norm_nonneg
    (completedForceAngular lower positive bounded parameters tangential source)
  have radialNonnegative := norm_nonneg
    (completedForceRadial lower positive bounded parameters tangential source)
  have fourthNonnegative := norm_nonneg
    (completedFourthSource lower positive bounded parameters L tangential source)
  constructor
  · linarith
  constructor <;> linarith

end Grad.SourceCollarBulk
