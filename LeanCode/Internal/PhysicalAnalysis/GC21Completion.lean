import GC21CoreMap

noncomputable section

namespace Grad.GaugeCoefficients.Physical.WeightedTrace

open Grad.ClosedJets Grad.GaugeCoefficients.Physical.RadialLedger Grad.BoundaryTrace

theorem apBoundaryTrace_exists {dimension : ℕ} (L sigma gamma ell : ℝ)
    (grade : ℕ) (gradePositive : 1 ≤ grade) :
    ∃ trace : apGrade L sigma gamma ell dimension grade →L[ℂ]
        APBoundaryGrade L sigma gamma ell dimension grade,
      (∀ core, trace (apFiniteInto L sigma gamma ell core) = apCoreTraceLinear L sigma gamma ell grade gradePositive core) ∧
      (∀ field, ‖trace field‖ ≤ Real.sqrt (traceCellConstant grade) * ‖field‖) :=
  apDense_extension (apFiniteInto L sigma gamma ell) (apFiniteInto_injective L sigma gamma ell)
    (apFiniteInto_denseRange L sigma gamma ell) (apCoreTraceLinear L sigma gamma ell grade gradePositive)
    (Real.sqrt (traceCellConstant grade)) (Real.sqrt_nonneg _)
    (apCoreTraceLinear_norm_le L sigma gamma ell grade gradePositive)

/-- The actual trace on the original AP2 closed derivative graph. -/
def apBoundaryTrace {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ) (gradePositive : 1 ≤ grade) :
    apGrade L sigma gamma ell dimension grade →L[ℂ] APBoundaryGrade L sigma gamma ell dimension grade :=
  (apBoundaryTrace_exists L sigma gamma ell grade gradePositive).choose

theorem apBoundaryTrace_core {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (core : ℤ →₀ ClosedJet dimension) :
    apBoundaryTrace L sigma gamma ell grade gradePositive (apFiniteInto L sigma gamma ell core) =
      apCoreTraceLinear L sigma gamma ell grade gradePositive core :=
  (apBoundaryTrace_exists L sigma gamma ell grade gradePositive).choose_spec.1 core

theorem apBoundaryTrace_coefficient {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (core : ℤ →₀ ClosedJet dimension) (mode : ℤ × ℤ) :
    apBoundaryCoefficient L sigma gamma ell grade
      (apBoundaryTrace L sigma gamma ell grade gradePositive (apFiniteInto L sigma gamma ell core)) mode =
      apCoreBoundaryCoefficient core mode := by
  rw [apBoundaryTrace_core, apCoreTraceLinear_coefficient]

theorem apBoundaryTrace_bound {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (field : apGrade L sigma gamma ell dimension grade) :
    ‖apBoundaryTrace L sigma gamma ell grade gradePositive field‖ ≤ Real.sqrt (traceCellConstant grade) * ‖field‖ :=
  (apBoundaryTrace_exists L sigma gamma ell grade gradePositive).choose_spec.2 field

theorem apBoundaryTrace_unique {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (gradePositive : 1 ≤ grade)
    (trace : apGrade L sigma gamma ell dimension grade →L[ℂ] APBoundaryGrade L sigma gamma ell dimension grade)
    (coreLaw : ∀ core, trace (apFiniteInto L sigma gamma ell core) =
      apCoreTraceLinear L sigma gamma ell grade gradePositive core) :
    trace = apBoundaryTrace L sigma gamma ell grade gradePositive := by
  apply ContinuousLinearMap.ext
  intro field
  apply isClosed_property (apFiniteInto_denseRange (dimension := dimension) (grade := grade) L sigma gamma ell)
    (isClosed_eq trace.continuous (apBoundaryTrace L sigma gamma ell grade gradePositive).continuous) _ field
  intro core
  rw [coreLaw, apBoundaryTrace_core]

theorem actualAPTraceGoal : APTraceGoal := by
  intro grade gradePositive
  refine ⟨Real.sqrt (traceCellConstant grade), Real.sqrt_nonneg _, ?_⟩
  intro L sigma gamma ell _ dimension
  exact ⟨apBoundaryTrace L sigma gamma ell grade gradePositive,
    apBoundaryTrace_coefficient L sigma gamma ell grade gradePositive,
    apBoundaryTrace_bound L sigma gamma ell grade gradePositive⟩

end Grad.GaugeCoefficients.Physical.WeightedTrace
