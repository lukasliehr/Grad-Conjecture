import SCD29GraphNorm

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace

/-- The actual original weighted quotient, in the exact nu^p and sqrt(r)
coordinates of the complete radial weak derivative graph. -/
def RepresentsFlatQuotient {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (parameters : PhaseParameters) (power radial : ℕ)
    (field : AGrade parameters dimension (power + radial + 3))
    (result : annularDerivativeGraph dimension lower positive radial) : Prop :=
  ∀ mode : ℤ × ℤ, ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1,
    result.val 0 mode radius =
      ((annularFrequency mode.1 mode.2 : ℂ) ^ power) • (Real.sqrt radius •
        angularCoefficient (fun angle =>
          cartesianWeight parameters mode.2 (polarPlane (radius, angle)) •
            (radius⁻¹ • completedOriginalCell parameters (by omega) mode.2 field
              (polarClosedPoint radius angle (positive.le.trans inside.1) inside.2))) mode.1)

theorem RepresentsFlatQuotient.unique {dimension : ℕ}
    {lower : ℝ} {positive : 0 < lower} {parameters : PhaseParameters} {power radial : ℕ}
    {field : AGrade parameters dimension (power + radial + 3)}
    {first second : annularDerivativeGraph dimension lower positive radial}
    (firstLaw : RepresentsFlatQuotient lower positive parameters power radial field first)
    (secondLaw : RepresentsFlatQuotient lower positive parameters power radial field second) : first = second := by
  apply annularDerivativeGraph_ext
  apply lp.ext
  funext mode
  apply Lp.ext
  filter_upwards [firstLaw mode, secondLaw mode, ae_restrict_mem measurableSet_Icc]
    with radius firstValue secondValue inside
  exact (firstValue inside).trans (secondValue inside).symm

/-- BS34, second estimate: all cells, original phase and original completed
A-grade, only zero value trace, exactly p+k+3 grades, and one constant uniform
over every 0<a<=1/2. The target is an actual complete derivative graph, whose
norm is the sum of radial L2(r dr) norms, not a sum of pointwise suprema. -/
def FlatSourceDivisionGoal : Prop :=
  ∀ power radial : ℕ, ∃ constant : ℝ, 0 < constant ∧
    ∀ (dimension : ℕ) (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower),
      lower ≤ 1 / 2 →
      ∀ field : AGrade parameters dimension (power + radial + 3),
        OriginalValueFlat parameters (by omega) field →
        ∃ result : annularDerivativeGraph dimension lower positive radial,
          ‖result‖ ≤ constant * ‖field‖ ∧
          RepresentsFlatQuotient lower positive parameters power radial field result ∧
          ∀ other : annularDerivativeGraph dimension lower positive radial,
            RepresentsFlatQuotient lower positive parameters power radial field other → other = result

theorem actualFlatSourceDivision : FlatSourceDivisionGoal := by
  intro power radial
  refine ⟨divisionGraphConstant power radial + 1, by
    have := divisionGraphConstant_nonnegative power radial
    linarith, ?_⟩
  intro dimension parameters lower positive halfBounded field flat
  have bounded : lower ≤ 1 := by linarith
  let result := completedDivision lower positive bounded parameters power radial field
  have literal : RepresentsFlatQuotient lower positive parameters power radial field result :=
    completedDivision_flat_literal lower positive bounded parameters power radial field flat
  refine ⟨result, ?_, literal, fun other otherLiteral => otherLiteral.unique literal⟩
  exact (completedDivision_bound lower positive bounded parameters power radial field).trans
    (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg field))

end Grad.SourceCollarDivision
