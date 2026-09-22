import AEH6OriginalPhysicalBoundaryConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace Grad.AnnularCurrentBoundary

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.BoundaryTrace Grad.AxisCore Grad.RealFixedRanges
open Grad.AnnularVariational Grad.AnnularUniformBoundary
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse
open Grad.AnnularReconstruction Grad.GaugeCoefficients.Physical.Allocation

section ExactTerm

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (angular cell : ℕ) (state : BoundaryInverseState parameters L compact)

/-- The sesquilinear term with every accepted component exposed: the SAME
outer endpoint of the `b_m`-decoded field and the literal kernel `-T⁻¹N`
acting on BCI25's original retained vector. -/
theorem actualCurrentHighBoundaryForm_literal
    (field test : annularEnergySpace lower L positive) :
    actualCurrentHighBoundaryFormValue parameters L compact lower positive lowerHalf
      lengthPositive angular cell state field test =
    ∑' mode : ℤ × ℤ,
      inner ℂ
        (highBoundaryIntoPositive parameters angular cell
          (annularEnergyTrace lower L positive (lowerHalf.trans_lt (by norm_num))
            lengthPositive 1
            (Grad.AnnularTiltedReference.bEnergyDecode lower L positive test)) mode)
        (fullNegativeKernelAction parameters angular cell
          (actualRetainedBoundaryLiftKernel state)
          (originalRetainedBoundaryVector parameters L angular cell
            (actualCurrentHighOuterTrace parameters lower L positive lowerHalf
              lengthPositive angular cell field)) mode) := by
  rw [actualCurrentHighBoundaryFormValue_tsum]
  apply tsum_congr
  intro mode
  rw [actualCurrentHighOuterTrace_same parameters lower L positive lowerHalf
    lengthPositive angular cell test]
  rw [actualCurrentHighBoundaryD_kernel parameters L compact lower positive lowerHalf
    lengthPositive angular cell state field]

/-- BF11 consumer at the literal base boundary grade. The bound has one
physical `B_8`, two exact energy norms, and a constant independent of `lower`. -/
theorem actualCurrentHighBoundary_BF11_consumer
    (field test : annularEnergySpace lower L positive) :
    actualCurrentHighOuterTrace parameters lower L positive lowerHalf
        lengthPositive 0 0 field =
      highBoundaryIntoPositive parameters 0 0
        (annularEnergyTrace lower L positive (lowerHalf.trans_lt (by norm_num))
          lengthPositive 1
          (Grad.AnnularTiltedReference.bEnergyDecode lower L positive field)) ∧
    actualCurrentHighBoundaryD parameters L compact lower positive lowerHalf
        lengthPositive 0 0 state field =
      actualRetainedBoundaryTerm state 0 0
        (originalRetainedBoundaryVector parameters L 0 0
          (actualCurrentHighOuterTrace parameters lower L positive lowerHalf
            lengthPositive 0 0 field)) ∧
    actualCurrentHighBoundaryFormValue parameters L compact lower positive lowerHalf
        lengthPositive 0 0 state field test =
      inner ℂ
        (actualCurrentHighOuterTrace parameters lower L positive lowerHalf
          lengthPositive 0 0 test)
        (actualCurrentHighBoundaryD parameters L compact lower positive lowerHalf
          lengthPositive 0 0 state field).val ∧
    ‖actualCurrentHighBoundaryFormValue parameters L compact lower positive lowerHalf
      lengthPositive 0 0 state field test‖ ≤
      actualCurrentHighBoundaryFormConstant parameters L compact 0 0 *
        physicalBudget parameters state.val.val.field state.val.val.rho
          state.val.val.epsilon 8 * ‖field‖ * ‖test‖ :=
  ⟨actualCurrentHighOuterTrace_same parameters lower L positive lowerHalf
      lengthPositive 0 0 field,
    actualCurrentHighBoundaryD_apply parameters L compact lower positive lowerHalf
      lengthPositive 0 0 state field,
    rfl,
    actualCurrentHighBoundaryForm_B8 parameters L compact lower positive lowerHalf
      lengthPositive state field test⟩

end ExactTerm

section FullPhysical

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (angular cell : ℕ) (large : 3 ≤ angular + cell + 2)
    (state : RetainedInverseState parameters L compact)

/-- General-grade consumer pairing the uniform boundary estimate with the
unchanged AHV10 physical boundary/sourceRange equivalence. -/
theorem actualCurrentHighBoundary_fullPhysical_consumer
    (field test : annularEnergySpace lower L positive)
    (x datum : HighBoundaryPrimitive parameters angular cell)
    (source : sourceRange parameters (angular + cell + 2) large) :
    ‖actualCurrentHighBoundaryFormValue parameters L compact lower positive lowerHalf
      lengthPositive angular cell state.outerInverseState field test‖ ≤
      actualCurrentHighBoundaryFormConstant parameters L compact angular cell *
        state.outerInverseState.val.budget (angular + cell + 1) * ‖field‖ * ‖test‖ ∧
    (physicalBoundaryFromPrescribedSource parameters L
        state.boundaryState.val.rho state.boundaryState.val.alpha
        state.boundaryState.val.delta state.boundaryState.val.parameter
        state.boundaryState.val.epsilon compact state.boundaryState.val.field
        state.boundaryState.property state.boundaryState.val.compactNonnegative
        state.boundaryState.val.alphaSmall state.boundaryState.val.deltaSmall
        state.boundaryState.val.parameterSmall angular cell large
        ⟨x.val, x.property.meanFree⟩
        (actualCurrentHighOuterTrace parameters lower L positive lowerHalf
          lengthPositive angular cell field) source = datum ↔
      x = actualCurrentHighBoundaryD parameters L compact lower positive lowerHalf
            lengthPositive angular cell state.outerInverseState field +
        (actualBoundaryInverseOnHigh state.outerInverseState angular cell datum +
          originalSourceBoundaryLiftOnHigh state.outerInverseState angular cell source.val)) :=
  ⟨actualCurrentHighBoundaryForm_bound parameters L compact lower positive lowerHalf
      lengthPositive angular cell state.outerInverseState field test,
    actualCurrentHighBoundary_originalPhysical_iff parameters L compact lower positive
      lowerHalf lengthPositive angular cell large state field x datum source⟩

end FullPhysical

end Grad.AnnularCurrentBoundary
