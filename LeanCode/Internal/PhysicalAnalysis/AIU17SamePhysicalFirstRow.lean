import AIU16OriginalPhysicalCoupledUniqueness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Grad.AnnularFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentSource Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularCrossMaps
open Grad.AnnularCoupledInverse Grad.AnnularKnownLow Grad.AnnularPhysicalSolution Grad.AnnularCurrentGreen Grad.AnnularKernelL2
open Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters L compact)
    (highData : ActualHighGraphKnownData parameters lower 0 0) (lowData : KnownLowData lower)

/-- The final actual physical first output solves the original completed
first row, with the SAME final high field and known-plus-low-cross datum. -/
theorem coupledPhysicalOutput_firstRow :
    retainedAAction parameters 0 lower positive (lowerHalf.trans (by norm_num)) L compact state
      (bulkMatrixUnit lower (0 : Fin 1) (0 : Fin 3)
        (coupledPhysicalOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData)) =
    eliminationRightHandAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0
      (fullHighEightPacket parameters lower L positive lengthPositive widthHalf widthLength
        ((coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).ofLp.1.ofLp.1,
          (coupledHighData parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).weighted)) := by
  unfold coupledPhysicalOutput
  rw [actualFullHighOutput_first]
  exact congrArg (fun action : DivisionRow 8 lower →L[ℂ] DivisionRow 1 lower => action
    (fullHighEightPacket parameters lower L positive lengthPositive widthHalf widthLength
      ((coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).ofLp.1.ofLp.1,
        (coupledHighData parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).weighted)))
    (eliminatedXAction_solves parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0)

/-- The flux used inside the high-to-low cross map is exactly the flux
reconstructed in the final coupled physical packet. -/
theorem coupledPhysicalOutput_sameFlux :
    (coupledKnownResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).ofLp.1.ofLp.2.val 0 =
    highPhysicalOutput lower 0
      (coupledPhysicalOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData) :=
  (coupledKnownResponse_high parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small highData lowData).2.2

end Grad.AnnularFullSource
