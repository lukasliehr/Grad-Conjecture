import GC20WeakGraph
import GC21Multiplier

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.WeightedTrace

open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.BoundaryTrace

/-- CT_GC20: one collar constant works for the full H¹ graph and all literal
angular/cell frequencies, including both zero modes. -/
theorem actualScalarCollarTrace (Value : Type*) [NormedAddCommGroup Value]
    [InnerProductSpace ℝ Value] [CompleteSpace Value] (lower : ℝ) (lowerOne : lower < 1) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ L ell : ℝ, ∀ mode : ℤ × ℤ, ∀ field : CollarH1 Value lower,
      ‖collarH1Trace Value lower lowerOne field‖ ^ 2 ≤ constant *
        (apBoundaryFrequency L ell mode * (∫ point in Icc lower 1, ‖collarH1Coordinate Value lower 0 field point‖ ^ 2) +
          (apBoundaryFrequency L ell mode)⁻¹ * (∫ point in Icc lower 1, ‖collarH1Coordinate Value lower 1 field point‖ ^ 2)) := by
  refine ⟨collarTraceConstant lower, zero_le_one.trans (collarTraceConstant_one_le lowerOne), ?_⟩
  intro L ell mode field
  exact scalar_collar_H1_integral_trace Value lower (apBoundaryFrequency L ell mode) lowerOne
    (apBoundaryFrequency_one_le L ell mode) field

/-- The finite complex physical H¹ graph is faithfully realized by its
zeroth L² coordinate; no independent derivative component remains. -/
theorem actualPhysicalCollarFaithful (dimension : ℕ) (lower : ℝ) (lowerOne : lower < 1) :
    letI := InnerProductSpace.rclikeToReal ℂ (PhysicalValue dimension)
    Function.Injective (collarH1Coordinate (PhysicalValue dimension) lower 0) :=
  collarH1_value_injective lower lowerOne.le

theorem apHighTrace_core_coefficient {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (core : ℤ →₀ ClosedJet dimension) (mode : ℤ × ℤ) :
    apBoundaryCoefficient L sigma gamma ell grade
      (apHighTrace L sigma gamma ell grade gradePositive (apFiniteInto L sigma gamma ell core)) mode =
      if 3 ≤ |mode.1| then apCoreBoundaryCoefficient core mode else 0 := by
  change apBoundaryCoefficient L sigma gamma ell grade
    (apHighProjection L sigma gamma ell grade
      (apBoundaryTrace L sigma gamma ell grade gradePositive (apFiniteInto L sigma gamma ell core))) mode = _
  rw [apHighProjection_coefficient, apBoundaryTrace_coefficient]

/-- CT_GC21: actual original AP2 trace, genuine high-angular projection,
and the bulk-first coefficient multiplier. The constants do not depend on
ell, the cell indices, or the value dimension. -/
def WeightedHalfOrderTraceGoal : Prop :=
  APTraceGoal ∧
    ∀ (L sigma gamma : ℝ) (grade : ℕ), ∀ gradePositive : 1 ≤ grade,
      ∃ traceConstant productConstant : ℝ, 0 ≤ traceConstant ∧
        ∀ ell : ℝ, ∀ admissible : Admissible L sigma gamma ell,
          0 ≤ productConstant ∧ ∀ input output : ℕ,
          (∀ field : apGrade L sigma gamma ell output grade,
            ‖apHighTrace L sigma gamma ell grade gradePositive field‖ ≤ traceConstant * ‖field‖) ∧
          (∀ (coefficient : Coefficient L sigma gamma ell grade input output)
              (field : apGrade L sigma gamma ell input grade),
            ‖apMultiplierTrace admissible gradePositive coefficient field‖ ≤
              productConstant * ‖coefficient‖ * ‖field‖ ∧
            ‖apHighProjection L sigma gamma ell grade
              (apMultiplierTrace admissible gradePositive coefficient field)‖ ≤
              productConstant * ‖coefficient‖ * ‖field‖)

theorem actualWeightedHalfOrderTrace : WeightedHalfOrderTraceGoal := by
  refine ⟨actualAPTraceGoal, ?_⟩
  intro L sigma gamma grade gradePositive
  refine ⟨Real.sqrt (traceCellConstant grade),
    Real.sqrt (traceCellConstant grade) * apMultiplierConstant L sigma gamma grade,
    Real.sqrt_nonneg _, ?_⟩
  intro ell admissible
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (apMultiplierConstant_nonnegative admissible grade), ?_⟩
  intro input output
  refine ⟨apHighTrace_bound L sigma gamma ell grade gradePositive, ?_⟩
  intro coefficient field
  exact ⟨apMultiplierTrace_bound admissible gradePositive coefficient field,
    apHighMultiplierTrace_bound admissible gradePositive coefficient field⟩

/-- Exact norm/realization consumer at arbitrary grade and physical value
dimension. This exposes the original AP3 sum, not an equivalent norm. -/
theorem actualWeightedTrace_energy {dimension grade : ℕ} (L sigma gamma ell : ℝ)
    (gradePositive : 1 ≤ grade) (field : apGrade L sigma gamma ell dimension grade) :
    (∑' mode : ℤ × ℤ, Real.exp (2 * apBoundaryPhase sigma gamma ell mode.2) *
      apBoundaryFrequency L ell mode ^ (2 * grade - 1) *
        ‖apBoundaryCoefficient L sigma gamma ell grade
          (apBoundaryTrace L sigma gamma ell grade gradePositive field) mode‖ ^ 2) ≤
      traceCellConstant grade * ‖field‖ ^ 2 := by
  rw [← apBoundary_norm_sq L sigma gamma ell grade]
  have bound := apBoundaryTrace_bound L sigma gamma ell grade gradePositive field
  have square := mul_self_le_mul_self (norm_nonneg _) bound
  simpa only [← pow_two, mul_pow, Real.sq_sqrt (traceCellConstant_nonnegative grade)] using square

end Grad.GaugeCoefficients.Physical.WeightedTrace
