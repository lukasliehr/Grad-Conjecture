import AEH4ActualHighBoundaryD

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped BigOperators

namespace Grad.AnnularCurrentBoundary

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.AnnularVariational Grad.AnnularUniformBoundary
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse
open Grad.GaugeCoefficients.Physical.Allocation

section Form

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (angular cell : ℕ) (state : BoundaryInverseState parameters L compact)

/-- The eliminated current boundary contribution paired in the reciprocal
AH16 positive/negative-half Hilbert coordinates. It is complex-linear in
`field` and conjugate-linear in `test`. -/
def actualCurrentHighBoundaryFormValue
    (field test : annularEnergySpace lower L positive) : ℂ :=
  inner ℂ
    (actualCurrentHighOuterTrace parameters lower L positive lowerHalf
      lengthPositive angular cell test)
    (actualCurrentHighBoundaryD parameters L compact lower positive lowerHalf
      lengthPositive angular cell state field).val

theorem actualCurrentHighBoundaryFormValue_add_field
    (first second test : annularEnergySpace lower L positive) :
    actualCurrentHighBoundaryFormValue parameters L compact lower positive lowerHalf
      lengthPositive angular cell state (first + second) test =
    actualCurrentHighBoundaryFormValue parameters L compact lower positive lowerHalf
        lengthPositive angular cell state first test +
      actualCurrentHighBoundaryFormValue parameters L compact lower positive lowerHalf
        lengthPositive angular cell state second test := by
  unfold actualCurrentHighBoundaryFormValue
  rw [map_add]
  change inner ℂ _ (_ + _) = _
  rw [inner_add_right]

theorem actualCurrentHighBoundaryFormValue_smul_field
    (scalar : ℂ) (field test : annularEnergySpace lower L positive) :
    actualCurrentHighBoundaryFormValue parameters L compact lower positive lowerHalf
      lengthPositive angular cell state (scalar • field) test =
    scalar * actualCurrentHighBoundaryFormValue parameters L compact lower positive
      lowerHalf lengthPositive angular cell state field test := by
  unfold actualCurrentHighBoundaryFormValue
  rw [map_smul]
  change inner ℂ _ (scalar • _) = _
  rw [inner_smul_right]

theorem actualCurrentHighBoundaryFormValue_add_test
    (field first second : annularEnergySpace lower L positive) :
    actualCurrentHighBoundaryFormValue parameters L compact lower positive lowerHalf
      lengthPositive angular cell state field (first + second) =
    actualCurrentHighBoundaryFormValue parameters L compact lower positive lowerHalf
        lengthPositive angular cell state field first +
      actualCurrentHighBoundaryFormValue parameters L compact lower positive lowerHalf
        lengthPositive angular cell state field second := by
  simp only [actualCurrentHighBoundaryFormValue, map_add, inner_add_left]

theorem actualCurrentHighBoundaryFormValue_smul_test
    (scalar : ℂ) (field test : annularEnergySpace lower L positive) :
    actualCurrentHighBoundaryFormValue parameters L compact lower positive lowerHalf
      lengthPositive angular cell state field (scalar • test) =
    starRingEnd ℂ scalar *
      actualCurrentHighBoundaryFormValue parameters L compact lower positive lowerHalf
        lengthPositive angular cell state field test := by
  simp only [actualCurrentHighBoundaryFormValue, map_smul, inner_smul_left]

/-- Literal all-mode expansion of the completed reciprocal trace pairing. -/
theorem actualCurrentHighBoundaryFormValue_tsum
    (field test : annularEnergySpace lower L positive) :
    actualCurrentHighBoundaryFormValue parameters L compact lower positive lowerHalf
      lengthPositive angular cell state field test =
    ∑' mode : ℤ × ℤ,
      inner ℂ
        (actualCurrentHighOuterTrace parameters lower L positive lowerHalf
          lengthPositive angular cell test mode)
        ((actualCurrentHighBoundaryD parameters L compact lower positive lowerHalf
          lengthPositive angular cell state field).val mode) := by
  rw [actualCurrentHighBoundaryFormValue, lp.inner_eq_tsum]

def actualCurrentHighBoundaryFormConstant : ℝ :=
  uniformOuterTraceConstant L *
    actualCurrentHighBoundaryDConstant parameters L compact angular cell

theorem actualCurrentHighBoundaryFormConstant_nonnegative :
    0 ≤ actualCurrentHighBoundaryFormConstant parameters L compact angular cell :=
  mul_nonneg (uniformOuterTraceConstant_nonnegative L)
    (actualCurrentHighBoundaryDConstant_nonnegative parameters L compact angular cell)

/-- Uniform boundary-form estimate at every split tangential grade. -/
theorem actualCurrentHighBoundaryForm_bound
    (field test : annularEnergySpace lower L positive) :
    ‖actualCurrentHighBoundaryFormValue parameters L compact lower positive lowerHalf
      lengthPositive angular cell state field test‖ ≤
    actualCurrentHighBoundaryFormConstant parameters L compact angular cell *
      state.val.budget (angular + cell + 1) * ‖field‖ * ‖test‖ := by
  have pairing := norm_inner_le_norm (𝕜 := ℂ)
    (actualCurrentHighOuterTrace parameters lower L positive lowerHalf
      lengthPositive angular cell test)
    (actualCurrentHighBoundaryD parameters L compact lower positive lowerHalf
      lengthPositive angular cell state field).val
  have traceBound := actualCurrentHighOuterTrace_bound parameters lower L positive
    lowerHalf lengthPositive angular cell test
  have operatorBound := actualCurrentHighBoundaryD_bound parameters L compact lower
    positive lowerHalf lengthPositive angular cell state field
  apply pairing.trans
  calc
    ‖actualCurrentHighOuterTrace parameters lower L positive lowerHalf
        lengthPositive angular cell test‖ *
      ‖(actualCurrentHighBoundaryD parameters L compact lower positive lowerHalf
        lengthPositive angular cell state field).val‖ ≤
      (uniformOuterTraceConstant L * ‖test‖) *
        (actualCurrentHighBoundaryDConstant parameters L compact angular cell *
          state.val.budget (angular + cell + 1) * ‖field‖) := by
      exact mul_le_mul traceBound operatorBound (norm_nonneg _)
        (mul_nonneg (uniformOuterTraceConstant_nonnegative L) (norm_nonneg test))
    _ = actualCurrentHighBoundaryFormConstant parameters L compact angular cell *
        state.val.budget (angular + cell + 1) * ‖field‖ * ‖test‖ := by
      unfold actualCurrentHighBoundaryFormConstant
      ring

/-- BF11 at base grade: one literal `B_8` factor and no collar loss. -/
theorem actualCurrentHighBoundaryForm_B8
    (field test : annularEnergySpace lower L positive) :
    ‖actualCurrentHighBoundaryFormValue parameters L compact lower positive lowerHalf
      lengthPositive 0 0 state field test‖ ≤
    actualCurrentHighBoundaryFormConstant parameters L compact 0 0 *
      physicalBudget parameters state.val.val.field state.val.val.rho
        state.val.val.epsilon 8 * ‖field‖ * ‖test‖ := by
  simpa only [zero_add, Nat.reduceAdd] using
    actualCurrentHighBoundaryForm_bound parameters L compact lower positive lowerHalf
      lengthPositive 0 0 state field test

end Form

end Grad.AnnularCurrentBoundary
