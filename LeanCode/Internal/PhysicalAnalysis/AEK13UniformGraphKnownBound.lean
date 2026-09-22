import AEK12GraphNativeKnownFunctional

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators

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

section Quantitative

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (angular cell : ℕ)

/-- Uniform bound for the complete graph-native known boundary vector. -/
theorem actualHighGraphBoundaryVector_bound
    (graphs : HighRadialSourceGraphs parameters lower (angular + cell))
    (datum : HighBoundaryPrimitive parameters angular cell) :
    ‖actualHighGraphBoundaryVector state.outerInverseState angular cell datum
      (highGraphOuterTuple parameters lower positive
        (lowerHalf.trans_lt (by norm_num)) (angular + cell) graphs)‖ ≤
      knownBoundaryInverseConstant parameters L compact (angular + cell + 1) *
          state.outerInverseState.val.val.size (angular + cell + 1) * ‖datum‖ +
        graphSourceLiftMomentConstant parameters L compact (angular + cell + 1) *
          state.outerInverseState.val.val.size (angular + cell + 1) *
          fullKernelMoment parameters (angular + cell + 1)
            (sourceTupleProjectionKernel parameters) *
          uniformSourceOuterConstant * (2 * ‖graphs.1‖ + ‖graphs.2‖) := by
  apply (norm_add_le _ _).trans
  exact add_le_add
    (actualBoundaryInverseOnHigh_known_bound parameters L compact
      state.outerInverseState angular cell datum)
    (highGraphSourceBoundaryLiftOnHigh_bound parameters L compact lower positive
      lowerHalf state.outerInverseState angular cell graphs)

/-- BF13's collar-independent coefficient in the actual independent weighted
bulk norm, the physical datum norm, and the two genuine radial graph norms. -/
def actualHighGraphKnownFunctionalSize
    (known : HighKnownSourceBulk lower)
    (auxiliary : HighAuxiliarySourceBulk lower)
    (graphs : HighRadialSourceGraphs parameters lower (angular + cell))
    (datum : HighBoundaryPrimitive parameters angular cell) : ℝ :=
  5 * (4 * eliminatedBulkConstant parameters L compact 0 * state.val.val.size 0 * ‖known‖ +
      3 * ‖auxiliary‖) +
    uniformOuterTraceConstant L *
      (knownBoundaryInverseConstant parameters L compact (angular + cell + 1) *
          state.outerInverseState.val.val.size (angular + cell + 1) * ‖datum‖ +
        graphSourceLiftMomentConstant parameters L compact (angular + cell + 1) *
          state.outerInverseState.val.val.size (angular + cell + 1) *
          fullKernelMoment parameters (angular + cell + 1)
            (sourceTupleProjectionKernel parameters) *
          uniformSourceOuterConstant * (2 * ‖graphs.1‖ + ‖graphs.2‖))

theorem actualHighGraphKnownFunctionalSize_nonnegative
    (known : HighKnownSourceBulk lower)
    (auxiliary : HighAuxiliarySourceBulk lower)
    (graphs : HighRadialSourceGraphs parameters lower (angular + cell))
    (datum : HighBoundaryPrimitive parameters angular cell) :
    0 ≤ actualHighGraphKnownFunctionalSize parameters L compact lower state
      angular cell known auxiliary graphs datum := by
  have sizeZero := state.val.val.size_nonnegative 0
  have sizeGrade := state.outerInverseState.val.val.size_nonnegative
    (angular + cell + 1)
  unfold actualHighGraphKnownFunctionalSize
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
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (graphSourceLiftMomentConstant_nonnegative parameters L compact _)
              sizeGrade)
            (fullKernelMoment_nonnegative parameters _ _))
          uniformSourceOuterConstant_nonnegative)
        (add_nonneg (mul_nonneg (by norm_num) (norm_nonneg graphs.1))
          (norm_nonneg graphs.2)))))

/-- Uniform BF13 estimate for the literal complex known side.  The source
boundary term is controlled only by the two genuine graph norms. -/
theorem actualHighGraphKnownFunctionalValue_bound
    (known : HighKnownSourceBulk lower)
    (auxiliary : HighAuxiliarySourceBulk lower)
    (graphs : HighRadialSourceGraphs parameters lower (angular + cell))
    (datum : HighBoundaryPrimitive parameters angular cell)
    (test : annularEnergySpace lower L positive) :
    ‖actualHighGraphKnownFunctionalValue parameters L compact lower positive
      lowerHalf lengthPositive widthHalf widthLength state angular cell known
        auxiliary graphs datum test‖ ≤
      actualHighGraphKnownFunctionalSize parameters L compact lower state
        angular cell known auxiliary graphs datum * ‖test‖ := by
  let output := actualHighKnownBulkOutput parameters L compact lower positive
    (lowerHalf.trans (by norm_num)) state known auxiliary
  let boundary := actualHighGraphBoundaryVector state.outerInverseState angular cell datum
    (highGraphOuterTuple parameters lower positive
      (lowerHalf.trans_lt (by norm_num)) (angular + cell) graphs)
  have testBound := highEnergyTestPacket_bound parameters lower L positive
    lengthPositive widthHalf widthLength test
  have outputBound := actualHighKnownBulkOutput_bound parameters L compact lower
    positive lowerHalf state known auxiliary
  have bulk := (norm_inner_le_norm (𝕜 := ℂ)
    (highEnergyTestPacket parameters lower L positive lengthPositive
      widthHalf widthLength test) output).trans
    (mul_le_mul testBound outputBound (norm_nonneg output)
      (mul_nonneg (by norm_num) (norm_nonneg test)))
  have traceBound := actualCurrentHighOuterTrace_bound parameters lower L positive
    lowerHalf lengthPositive angular cell test
  have boundaryBound := actualHighGraphBoundaryVector_bound parameters L compact
    lower positive lowerHalf state angular cell graphs datum
  have edge := (norm_inner_le_norm (𝕜 := ℂ)
    (actualCurrentHighOuterTrace parameters lower L positive lowerHalf
      lengthPositive angular cell test) boundary.val).trans
    (mul_le_mul traceBound boundaryBound (norm_nonneg boundary)
      (mul_nonneg (uniformOuterTraceConstant_nonnegative L) (norm_nonneg test)))
  apply (norm_sub_le _ _).trans
  unfold actualHighGraphKnownFunctionalSize
  dsimp only [output, boundary] at bulk edge
  exact (add_le_add bulk edge).trans_eq (by ring)

theorem actualHighGraphKnownFunctional_apply_bound
    (known : HighKnownSourceBulk lower)
    (auxiliary : HighAuxiliarySourceBulk lower)
    (graphs : HighRadialSourceGraphs parameters lower (angular + cell))
    (datum : HighBoundaryPrimitive parameters angular cell)
    (test : annularEnergySpace lower L positive) :
    ‖actualHighGraphKnownFunctional parameters L compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state angular cell known auxiliary
        graphs datum test‖ ≤
      actualHighGraphKnownFunctionalSize parameters L compact lower state
        angular cell known auxiliary graphs datum * ‖test‖ := by
  rw [actualHighGraphKnownFunctional_literal, Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans
    (actualHighGraphKnownFunctionalValue_bound parameters L compact lower
      positive lowerHalf lengthPositive widthHalf widthLength state angular cell
      known auxiliary graphs datum test)

end Quantitative
end Grad.AnnularCurrentSource
