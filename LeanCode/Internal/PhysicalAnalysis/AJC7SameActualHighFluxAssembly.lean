import AJC6SharedHighSevenAssembly
import AIU17SamePhysicalFirstRow

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
namespace Grad.AnnularStrongSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource Grad.AnnularPhysicalSolution Grad.AnnularCurrentSolution
open Grad.AnnularCrossMaps Grad.AnnularKnownLow Grad.AnnularReconstruction Grad.AnnularFullSource
open Grad.AnnularCoupledInverse Grad.AnnularKernelL2 Grad.AnnularCurrentGreen
open Grad.GaugeCoefficients.Physical.Allocation

private theorem highOnly_recover (lower : ℝ) (field : DivisionRow 1 lower)
    (supported : ∀ mode : ℤ × ℤ, |mode.1| < 3 → field mode = 0) :
    highBulkIntoFull lower (highFullRestriction lower field) = field :=
  (highRowProjection_fixed_iff lower field).mpr (fun mode outside => supported mode (lt_of_not_ge outside))

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters L compact)
    (highData : ActualHighGraphKnownData parameters lower 0 0) (lowData : KnownLowData lower)

/-- The x coordinate consumed by the cross maps is the SAME full-space
first-row elimination, recovered from its genuine high support. -/
theorem coupledEliminatedX_same :
    let solution := coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData
    let data := coupledHighData parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData
    eliminatedXAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0
      (fullHighEightPacket parameters lower L positive lengthPositive widthHalf widthLength (solution.ofLp.1.ofLp.1, data.weighted)) =
      highBulkIntoFull lower (crossHighX lower L positive lengthPositive solution.ofLp.1) := by
  let solution := coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData
  let data := coupledHighData parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData
  let input := fullHighEightPacket parameters lower L positive lengthPositive widthHalf widthLength (solution.ofLp.1.ofLp.1, data.weighted)
  let x := eliminatedXAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 input
  have first : bulkMatrixUnit lower (0 : Fin 1) (0 : Fin 3)
      (actualFullHighOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
        solution.ofLp.1.ofLp.1 data.weighted data.auxiliary) = x :=
    actualFullHighOutput_first parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
      solution.ofLp.1.ofLp.1 data.weighted data.auxiliary
  have restricted : highFullRestriction lower x = crossHighX lower L positive lengthPositive solution.ofLp.1 :=
    (congrArg (highFullRestriction lower) first).symm.trans
      (coupledPhysicalOutput_sameFlux parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).symm
  have supported (mode : ℤ × ℤ) (low : |mode.1| < 3) : x mode = 0 := by
    change eliminatedXAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 input mode = 0
    rw [eliminatedXAction_eq_inverse]
    exact retainedInverseAction_high parameters 0 lower positive (lowerHalf.trans (by norm_num)) L compact state
      (eliminationRightHandAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 input) mode low
  exact (highOnly_recover lower x supported).symm.trans (congrArg (highBulkIntoFull lower) restricted)

/-- The eliminated seven-slot packet is exactly the final high field and
the three original known source entries, before adding the low field. -/
theorem coupledEliminatedSeven_same :
    let solution := coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData
    let data := coupledHighData parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData
    eliminatedSevenBulkAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0
      (fullHighEightPacket parameters lower L positive lengthPositive widthHalf widthLength (solution.ofLp.1.ofLp.1, data.weighted)) =
      highCrossSevenInput lower L positive lengthPositive solution.ofLp.1 + knownLowSevenPacket lower data.weighted := by
  dsimp only
  let solution := coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData
  let data := coupledHighData parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData
  let input := fullHighEightPacket parameters lower L positive lengthPositive widthHalf widthLength (solution.ofLp.1.ofLp.1, data.weighted)
  exact (eliminatedSevenBulkAction_assembled parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 input).trans
    ((congrArg (fun x : DivisionRow 1 lower => assembledSevenBulk parameters lower positive (lowerHalf.trans (by norm_num)) 0 x input)
      (coupledEliminatedX_same parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData)).trans
      (assembledSevenBulk_high parameters lower positive (lowerHalf.trans (by norm_num)) L lengthPositive widthHalf widthLength solution.ofLp.1 data.weighted))

end Grad.AnnularStrongSolution
