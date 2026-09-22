import ANS9OriginalSmoothInverse

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
open Set MeasureTheory
open scoped BigOperators
namespace Grad.ActualAngularInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra

variable {L sigma gamma ell : ℝ}

def apShiftedRotation (admissible : Admissible L sigma gamma ell)
    (dimension : ℕ) (shift : ℤ) : APSmooth L sigma gamma ell dimension →ₗ[ℂ] APSmooth L sigma gamma ell dimension :=
  apSmoothRotation admissible dimension +
    (Complex.I * (shift : ℂ)) • LinearMap.id

theorem apShiftedRotation_jet (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (shift : ℤ) (field : APSmooth L sigma gamma ell dimension) (cell : ℤ) :
    apSmoothJet admissible dimension cell (apShiftedRotation admissible dimension shift field) =
      shiftedRotationJet shift (apSmoothJet admissible dimension cell field) := by
  let project := apSmoothJet admissible dimension cell
  exact (project.map_add (apSmoothRotation admissible dimension field)
    ((Complex.I * (shift : ℂ)) • field)).trans
      (congrArg₂ (fun first second : ClosedJet dimension => first + second)
        (apSmoothRotation_jet admissible field cell)
        (project.map_smul (Complex.I * (shift : ℂ)) field))

def APNonresonant (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (shift : ℤ) (field : APSmooth L sigma gamma ell dimension) : Prop :=
  ∀ cell, angularClosedJet (-shift) (apSmoothJet admissible dimension cell field) = 0

theorem apShiftInverse_nonresonant (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (shift : ℤ) (field : APSmooth L sigma gamma ell dimension) :
    APNonresonant admissible shift (apShiftInverse admissible shift field) := by
  intro cell
  exact (congrArg (angularClosedJet (-shift)) (apShiftInverse_jet admissible shift field cell)).trans
    (shiftInverse_nonresonant shift _)

theorem apShiftInverse_solves (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (shift : ℤ) (field : APSmooth L sigma gamma ell dimension)
    (nonresonant : APNonresonant admissible shift field) :
    apShiftedRotation admissible dimension shift (apShiftInverse admissible shift field) = field := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apShiftedRotation_jet admissible shift (apShiftInverse admissible shift field) cell).trans
    ((congrArg (shiftedRotationJet shift) (apShiftInverse_jet admissible shift field cell)).trans
      (shiftInverse_solves shift _ (nonresonant cell)))

theorem apShiftInverse_unique (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (shift : ℤ) (source candidate : APSmooth L sigma gamma ell dimension)
    (nonresonant : APNonresonant admissible shift candidate)
    (equation : apShiftedRotation admissible dimension shift candidate = source) :
    candidate = apShiftInverse admissible shift source := by
  apply apSmoothJet_ext admissible
  intro cell
  have literal := (apShiftedRotation_jet admissible shift candidate cell).symm.trans
    (congrArg (apSmoothJet admissible dimension cell) equation)
  exact (shiftInverse_unique shift _ _ (nonresonant cell) literal).trans
    (apShiftInverse_jet admissible shift source cell).symm

private theorem graph_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (source solution rotated : E) (scalar : ℂ) (C : ℝ)
    (bound : ‖solution‖ ≤ C * ‖source‖) (equation : rotated + scalar • solution = source) :
    ‖solution‖ + ‖rotated‖ ≤ (1 + (1 + ‖scalar‖) * C) * ‖source‖ := by
  have equality : rotated = source - scalar • solution := eq_sub_of_add_eq equation
  have triangle := norm_sub_le source (scalar • solution)
  rw [← equality, norm_smul] at triangle
  have scaled := mul_le_mul_of_nonneg_left bound (norm_nonneg scalar)
  nlinarith

/-- The additional R slot costs no derivative: it comes from the exact equation. -/
theorem apShiftInverse_graph_bound (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (shift : ℤ) (source : APSmooth L sigma gamma ell dimension)
    (nonresonant : APNonresonant admissible shift source) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell dimension grade (apShiftInverse admissible shift source)‖ +
      ‖apSmoothGrade L sigma gamma ell dimension grade
        (apSmoothRotation admissible dimension (apShiftInverse admissible shift source))‖ ≤
      (1 + (1 + ‖Complex.I * (shift : ℂ)‖) * angularInverseConstant grade) *
        ‖apSmoothGrade L sigma gamma ell dimension grade source‖ := by
  let project := apSmoothGrade L sigma gamma ell dimension grade
  have equality := congrArg project (apShiftInverse_solves admissible shift source nonresonant)
  have expansion := (project.map_add
    (apSmoothRotation admissible dimension (apShiftInverse admissible shift source))
    ((Complex.I * (shift : ℂ)) • apShiftInverse admissible shift source)).trans
      (congrArg (fun second => project (apSmoothRotation admissible dimension
        (apShiftInverse admissible shift source)) + second)
        (project.map_smul (Complex.I * (shift : ℂ)) (apShiftInverse admissible shift source)))
  exact graph_bound _ _ _ _ _ (apShiftInverse_bound admissible shift grade source)
    (expansion.symm.trans equality)

/-- One actual smooth AP solution is chosen before all grades; its exact literal
R+i*shift equation and uniqueness retain the original phase, scale and width. -/
theorem actualOriginalAngularInverse (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (shift : ℤ) (source : APSmooth L sigma gamma ell dimension)
    (nonresonant : APNonresonant admissible shift source) :
    ∃! solution : APSmooth L sigma gamma ell dimension,
      APNonresonant admissible shift solution ∧
      apShiftedRotation admissible dimension shift solution = source ∧
      (∀ grade, ‖apSmoothGrade L sigma gamma ell dimension grade solution‖ ≤
        angularInverseConstant grade * ‖apSmoothGrade L sigma gamma ell dimension grade source‖) ∧
      (∀ grade, ‖apSmoothGrade L sigma gamma ell dimension grade solution‖ +
        ‖apSmoothGrade L sigma gamma ell dimension grade (apSmoothRotation admissible dimension solution)‖ ≤
        (1 + (1 + ‖Complex.I * (shift : ℂ)‖) * angularInverseConstant grade) *
          ‖apSmoothGrade L sigma gamma ell dimension grade source‖) := by
  refine ⟨apShiftInverse admissible shift source,
    ⟨apShiftInverse_nonresonant admissible shift source, apShiftInverse_solves admissible shift source nonresonant,
      fun grade => apShiftInverse_bound admissible shift grade source,
      apShiftInverse_graph_bound admissible shift source nonresonant⟩, ?_⟩
  intro candidate satisfies
  exact apShiftInverse_unique admissible shift source candidate satisfies.1 satisfies.2.1

end Grad.ActualAngularInverse
