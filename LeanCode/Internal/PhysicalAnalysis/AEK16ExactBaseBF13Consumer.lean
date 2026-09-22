import AEK15BaseB8KnownFunctional

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.AnnularCurrentSource

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.AxisCore Grad.RealFixedRanges
open Grad.AnnularVariational Grad.AnnularCurrentEnergy
open Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed
  Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed
  Grad.AnnularCurrentEnergy.energyRealModule

/-- Direct seven-slot source input derived from the genuine radial graphs.
It is available at base grade without a false `sourceRange parameters 2`
premise. -/
def ActualHighGraphKnownData.sourceSevenSlotTrace
    (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (angular cell : ℕ)
    (data : ActualHighGraphKnownData parameters lower angular cell) :
    SevenSlotTrace parameters angular cell :=
  sevenSlotTrace parameters angular cell 0 0
    (highGraphOuterTuple parameters lower positive
      (lowerHalf.trans_lt (by norm_num)) (angular + cell) data.graphs)

theorem ActualHighGraphKnownData.sourceSevenSlotTrace_components
    (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (angular cell : ℕ)
    (data : ActualHighGraphKnownData parameters lower angular cell) :
    (fun slot => data.sourceSevenSlotTrace parameters lower positive lowerHalf
      angular cell slot) =
      ![0, 0, 0, 0,
        sourceBoundaryToNegative parameters angular cell
          (highGraphOuterTuple parameters lower positive
            (lowerHalf.trans_lt (by norm_num)) (angular + cell) data.graphs 0),
        sourceBoundaryToNegative parameters angular cell
          (highGraphOuterTuple parameters lower positive
            (lowerHalf.trans_lt (by norm_num)) (angular + cell) data.graphs 1),
        sourceBoundaryToNegative parameters angular cell
          (highGraphOuterTuple parameters lower positive
            (lowerHalf.trans_lt (by norm_num)) (angular + cell) data.graphs 2)] := by
  unfold ActualHighGraphKnownData.sourceSevenSlotTrace
  simpa using sevenSlotTrace_components parameters angular cell 0 0
    (highGraphOuterTuple parameters lower positive
      (lowerHalf.trans_lt (by norm_num)) (angular + cell) data.graphs)

/-- Boundary projection of the direct source seven-slot packet. -/
theorem ActualHighGraphKnownData.sourceBoundaryVector_direct
    (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (angular cell : ℕ)
    (data : ActualHighGraphKnownData parameters lower angular cell) :
    graphSourceBoundaryVector parameters angular cell
        (highGraphOuterTuple parameters lower positive
          (lowerHalf.trans_lt (by norm_num)) (angular + cell) data.graphs) =
      fullNegativeKernelAction parameters angular cell
        (sourceTupleProjectionKernel parameters)
        (sevenSlotFlatten parameters angular cell
          (data.sourceSevenSlotTrace parameters lower positive lowerHalf
            angular cell)) := rfl

section Base

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)

/-- Exact base-grade BF13 consumer: the real functional is the real part of
the literal complex AI14 known side, its solved boundary vector is
`T⁻¹ datum - T⁻¹ H(F0,RF0,F2)`, and its norm has the genuine B8
graph estimate. -/
theorem ActualHighGraphKnownData.exact_base_BF13
    (data : ActualHighGraphKnownData parameters lower 0 0) :
    (∀ test : annularEnergySpace lower L positive,
      data.functional parameters L compact lower positive lowerHalf
          lengthPositive widthHalf widthLength state 0 0 test =
        (actualHighGraphKnownFunctionalValue parameters L compact lower
          positive lowerHalf lengthPositive widthHalf widthLength state 0 0
          data.weighted data.auxiliary data.graphs data.datum test).re) ∧
    actualHighGraphBoundaryVector state.outerInverseState 0 0 data.datum
        (highGraphOuterTuple parameters lower positive
          (lowerHalf.trans_lt (by norm_num)) 0 data.graphs) =
      actualBoundaryInverseOnHigh state.outerInverseState 0 0 data.datum +
        actualSourceBoundaryTerm state.outerInverseState 0 0
          (graphSourceBoundaryVector parameters 0 0
            (highGraphOuterTuple parameters lower positive
              (lowerHalf.trans_lt (by norm_num)) 0 data.graphs)) ∧
    ‖data.zeroFunctional parameters L compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state 0 0‖ ≤
      actualHighGraphKnownB8Size parameters L compact lower state
        data.weighted data.auxiliary data.graphs data.datum := by
  refine ⟨?_, rfl, data.zeroFunctional_norm_base_B8 parameters L compact lower
    positive lowerHalf lengthPositive widthHalf widthLength state⟩
  intro test
  exact actualHighGraphKnownFunctional_literal parameters L compact lower
    positive lowerHalf lengthPositive widthHalf widthLength state 0 0
    data.weighted data.auxiliary data.graphs data.datum test

end Base
end Grad.AnnularCurrentSource
