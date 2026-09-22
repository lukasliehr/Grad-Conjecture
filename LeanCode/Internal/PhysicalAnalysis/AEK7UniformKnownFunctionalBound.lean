import AEK6CompleteSourceCompatibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal

namespace Grad.AnnularCurrentSource

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.AxisCore Grad.RealFixedRanges
open Grad.AnnularVariational Grad.AnnularUniformBoundary
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentBoundary
open Grad.AnnularKernelL2 Grad.AnnularReconstruction
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed
  Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed
  Grad.AnnularCurrentEnergy.energyRealModule

/-- Fixed moment constant for the actual high boundary inverse. -/
def knownBoundaryInverseConstant (parameters : PhaseParameters) (L compact : ℝ)
    (moment : ℕ) : ℝ :=
  Classical.choose (actualHighBoundaryInverse_physicalMoments parameters L compact moment)

theorem knownBoundaryInverseConstant_nonnegative (parameters : PhaseParameters)
    (L compact : ℝ) (moment : ℕ) :
    0 ≤ knownBoundaryInverseConstant parameters L compact moment :=
  (Classical.choose_spec
    (actualHighBoundaryInverse_physicalMoments parameters L compact moment)).1

theorem actualBoundaryInverseOnHigh_known_bound
    (parameters : PhaseParameters) (L compact : ℝ)
    (state : BoundaryInverseState parameters L compact) (angular cell : ℕ)
    (datum : HighBoundaryPrimitive parameters angular cell) :
    ‖actualBoundaryInverseOnHigh state angular cell datum‖ ≤
      knownBoundaryInverseConstant parameters L compact (angular + cell + 1) *
        state.val.val.size (angular + cell + 1) * ‖datum‖ := by
  change ‖fullNegativeKernelAction parameters angular cell
    (actualHighBoundaryInverse state.val state.property) datum.val‖ ≤ _
  apply (fullNegativeKernelAction_bound parameters angular cell
    (actualHighBoundaryInverse state.val state.property) datum.val).trans
  have moment := (Classical.choose_spec
    (actualHighBoundaryInverse_physicalMoments parameters L compact
      (angular + cell + 1))).2 state
  exact mul_le_mul_of_nonneg_right moment (norm_nonneg datum)

/-- Fixed original-source lift constant; it depends on the physical parameters
and split grade, but not on the collar radius. -/
def knownSourceLiftConstant (parameters : PhaseParameters) (L compact : ℝ)
    (lengthPositive : 0 < L) (angular cell : ℕ) : ℝ :=
  Classical.choose (originalSourceBoundaryLift_bound parameters L compact
    lengthPositive angular cell)

theorem knownSourceLiftConstant_nonnegative (parameters : PhaseParameters)
    (L compact : ℝ) (lengthPositive : 0 < L) (angular cell : ℕ) :
    0 ≤ knownSourceLiftConstant parameters L compact lengthPositive angular cell :=
  (Classical.choose_spec (originalSourceBoundaryLift_bound parameters L compact
    lengthPositive angular cell)).1

theorem originalSourceBoundaryLiftOnHigh_known_bound
    (parameters : PhaseParameters) (L compact : ℝ) (lengthPositive : 0 < L)
    (state : BoundaryInverseState parameters L compact) (angular cell : ℕ)
    (source : ZAmbient parameters (angular + cell + 2)) :
    ‖originalSourceBoundaryLiftOnHigh state angular cell source‖ ≤
      knownSourceLiftConstant parameters L compact lengthPositive angular cell *
        state.val.val.size (angular + cell + 1) * ‖source‖ := by
  change ‖originalSourceBoundaryLift state angular cell source‖ ≤ _
  simpa only [knownSourceLiftConstant, BoundaryReconstructionState.size,
    show angular + cell + 1 + 7 = angular + cell + 8 by omega] using
    (Classical.choose_spec (originalSourceBoundaryLift_bound parameters L compact
      lengthPositive angular cell)).2 state source

theorem actualHighKnownBoundaryVector_bound
    (parameters : PhaseParameters) (L compact : ℝ) (lengthPositive : 0 < L)
    (state : BoundaryInverseState parameters L compact) (angular cell : ℕ)
    (datum : HighBoundaryPrimitive parameters angular cell)
    (source : ZAmbient parameters (angular + cell + 2)) :
    ‖actualHighKnownBoundaryVector state angular cell datum source‖ ≤
      knownBoundaryInverseConstant parameters L compact (angular + cell + 1) *
          state.val.val.size (angular + cell + 1) * ‖datum‖ +
        knownSourceLiftConstant parameters L compact lengthPositive angular cell *
          state.val.val.size (angular + cell + 1) * ‖source‖ := by
  exact (norm_add_le _ _).trans (add_le_add
    (actualBoundaryInverseOnHigh_known_bound parameters L compact state angular cell datum)
    (originalSourceBoundaryLiftOnHigh_known_bound parameters L compact lengthPositive
      state angular cell source))

section Quantitative

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (angular cell : ℕ)

/-- Uniform known bulk estimate in the independently weighted BF2 norm. -/
theorem actualHighKnownBulkOutput_bound
    (known : HighKnownSourceBulk lower)
    (auxiliary : HighAuxiliarySourceBulk lower) :
    ‖actualHighKnownBulkOutput parameters L compact lower positive
      (lowerHalf.trans (by norm_num)) state known auxiliary‖ ≤
      4 * eliminatedBulkConstant parameters L compact 0 * state.val.val.size 0 * ‖known‖ +
        3 * ‖auxiliary‖ := by
  have packet := highKnownEightPacket_bound lower known
  have action := eliminatedBulkAction_bound parameters L compact lower positive
    (lowerHalf.trans (by norm_num)) state 0 (highKnownEightPacket lower known)
  have coefficientNonnegative :
      0 ≤ eliminatedBulkConstant parameters L compact 0 * state.val.val.size 0 :=
    mul_nonneg (eliminatedBulkConstant_nonnegative parameters L compact 0)
      (state.val.val.size_nonnegative 0)
  have action' := action.trans
    (mul_le_mul_of_nonneg_left packet coefficientNonnegative)
  have direct := directKnownThreePacket_bound lower positive auxiliary
  apply (norm_add_le _ _).trans
  calc
    ‖eliminatedBulkAction parameters L compact lower positive
        (lowerHalf.trans (by norm_num)) state 0 (highKnownEightPacket lower known)‖ +
      ‖directKnownThreePacket lower positive auxiliary‖ ≤
        (eliminatedBulkConstant parameters L compact 0 * state.val.val.size 0) *
          (4 * ‖known‖) + 3 * ‖auxiliary‖ := add_le_add action' direct
    _ = _ := by ring

/-- The complete collar-independent coefficient multiplying the test norm. -/
def actualHighKnownFunctionalSize
    (known : HighKnownSourceBulk lower)
    (auxiliary : HighAuxiliarySourceBulk lower)
    (datum : HighBoundaryPrimitive parameters angular cell)
    (source : ZAmbient parameters (angular + cell + 2)) : ℝ :=
  5 * (4 * eliminatedBulkConstant parameters L compact 0 * state.val.val.size 0 * ‖known‖ +
      3 * ‖auxiliary‖) +
    uniformOuterTraceConstant L *
      (knownBoundaryInverseConstant parameters L compact (angular + cell + 1) *
          state.outerInverseState.val.val.size (angular + cell + 1) * ‖datum‖ +
        knownSourceLiftConstant parameters L compact lengthPositive angular cell *
          state.outerInverseState.val.val.size (angular + cell + 1) * ‖source‖)

theorem actualHighKnownFunctionalSize_nonnegative
    (known : HighKnownSourceBulk lower)
    (auxiliary : HighAuxiliarySourceBulk lower)
    (datum : HighBoundaryPrimitive parameters angular cell)
    (source : ZAmbient parameters (angular + cell + 2)) :
    0 ≤ actualHighKnownFunctionalSize parameters L compact lower lengthPositive state
      angular cell known auxiliary datum source := by
  have sizeZero := state.val.val.size_nonnegative 0
  have sizeGrade := state.outerInverseState.val.val.size_nonnegative (angular + cell + 1)
  unfold actualHighKnownFunctionalSize
  exact add_nonneg
    (mul_nonneg (by norm_num) (add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        (eliminatedBulkConstant_nonnegative parameters L compact 0)) sizeZero)
        (norm_nonneg known))
      (mul_nonneg (by norm_num) (norm_nonneg auxiliary))))
    (mul_nonneg (uniformOuterTraceConstant_nonnegative L) (add_nonneg
      (mul_nonneg (mul_nonneg
        (knownBoundaryInverseConstant_nonnegative parameters L compact
          (angular + cell + 1)) sizeGrade) (norm_nonneg datum))
      (mul_nonneg (mul_nonneg
        (knownSourceLiftConstant_nonnegative parameters L compact lengthPositive angular cell)
        sizeGrade) (norm_nonneg source))))

theorem actualHighKnownFunctionalValue_bound
    (known : HighKnownSourceBulk lower)
    (auxiliary : HighAuxiliarySourceBulk lower)
    (datum : HighBoundaryPrimitive parameters angular cell)
    (source : ZAmbient parameters (angular + cell + 2))
    (test : annularEnergySpace lower L positive) :
    ‖actualHighKnownFunctionalValue parameters L compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state angular cell known auxiliary datum source test‖ ≤
      actualHighKnownFunctionalSize parameters L compact lower lengthPositive state
        angular cell known auxiliary datum source * ‖test‖ := by
  let output := actualHighKnownBulkOutput parameters L compact lower positive
    (lowerHalf.trans (by norm_num)) state known auxiliary
  let boundary := actualHighKnownBoundaryVector state.outerInverseState angular cell datum source
  have testBound := highEnergyTestPacket_bound parameters lower L positive lengthPositive
    widthHalf widthLength test
  have outputBound := actualHighKnownBulkOutput_bound parameters L compact lower positive
    lowerHalf state known auxiliary
  have bulk := (norm_inner_le_norm (𝕜 := ℂ)
    (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test)
    output).trans (mul_le_mul testBound outputBound (norm_nonneg output)
      (mul_nonneg (by norm_num) (norm_nonneg test)))
  have traceBound := actualCurrentHighOuterTrace_bound parameters lower L positive
    lowerHalf lengthPositive angular cell test
  have boundaryBound := actualHighKnownBoundaryVector_bound parameters L compact
    lengthPositive state.outerInverseState angular cell datum source
  have edge := (norm_inner_le_norm (𝕜 := ℂ)
    (actualCurrentHighOuterTrace parameters lower L positive lowerHalf
      lengthPositive angular cell test) boundary.val).trans
    (mul_le_mul traceBound boundaryBound (norm_nonneg boundary)
      (mul_nonneg (uniformOuterTraceConstant_nonnegative L) (norm_nonneg test)))
  apply (norm_sub_le _ _).trans
  unfold actualHighKnownFunctionalSize
  dsimp only [output, boundary] at bulk edge
  exact (add_le_add bulk edge).trans_eq (by ring)

theorem actualHighKnownFunctional_apply_bound
    (known : HighKnownSourceBulk lower)
    (auxiliary : HighAuxiliarySourceBulk lower)
    (datum : HighBoundaryPrimitive parameters angular cell)
    (source : ZAmbient parameters (angular + cell + 2))
    (test : annularEnergySpace lower L positive) :
    ‖actualHighKnownFunctional parameters L compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state angular cell known auxiliary datum source test‖ ≤
      actualHighKnownFunctionalSize parameters L compact lower lengthPositive state
        angular cell known auxiliary datum source * ‖test‖ := by
  rw [actualHighKnownFunctional_literal, Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans
    (actualHighKnownFunctionalValue_bound parameters L compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state angular cell known auxiliary datum source test)

end Quantitative
end Grad.AnnularCurrentSource
