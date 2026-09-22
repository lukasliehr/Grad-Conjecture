import AIE1ActualHighEnergySourceSolution

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.AnnularCurrentSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse Grad.AnnularCurrentSource
open Grad.AnnularKernelL2 Grad.AnnularCurrentBoundary Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.RealFixedRanges Grad.AxisCore Grad.SourceBoundaryTrace

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)

/-- Full actual three-output packet, including eliminated known sources and
the literal direct `(0,qc,rqv-rg)` forcing. -/
def actualFullHighOutput (field : annularEnergySpace lower L positive)
    (known : HighKnownSourceBulk lower) (auxiliary : HighAuxiliarySourceBulk lower) : DivisionRow 3 lower :=
  eliminatedBulkAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0
    (highEightEnergyPacket parameters lower L positive lengthPositive widthHalf widthLength field) +
    actualHighKnownBulkOutput parameters L compact lower positive (lowerHalf.trans (by norm_num)) state known auxiliary

/-- The completed full packet uses AHW once on the exact original eight
inputs, with no changed reconstruction or introduced source derivative. -/
theorem actualFullHighOutput_one_packet (field : annularEnergySpace lower L positive)
    (known : HighKnownSourceBulk lower) (auxiliary : HighAuxiliarySourceBulk lower) :
    actualFullHighOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field known auxiliary =
      eliminatedBulkAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0
        (fullHighEightPacket parameters lower L positive lengthPositive widthHalf widthLength (field, known)) +
        directKnownThreePacket lower positive auxiliary := by
  change _ + (_ + _) = eliminatedBulkAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0
    (highEightEnergyPacket parameters lower L positive lengthPositive widthHalf widthLength field + highKnownEightPacket lower known) + _
  rw [map_add]
  exact (add_assoc _ _ _).symm

/-- Algebraic weak correspondence for any literal known outer vector. This
also applies directly to the graph-native source tuple at base grade zero. -/
theorem actualFullHighOutput_variational
    (field test : annularEnergySpace lower L positive)
    (known : HighKnownSourceBulk lower) (auxiliary : HighAuxiliarySourceBulk lower)
    (knownBoundary : HighBoundaryPrimitive parameters 0 0)
    (equation : currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field test =
      inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test)
        (actualHighKnownBulkOutput parameters L compact lower positive (lowerHalf.trans (by norm_num)) state known auxiliary) -
      inner ℂ (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test) knownBoundary.val) :
    inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test)
      (actualFullHighOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field known auxiliary) =
    inner ℂ (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test)
      ((actualCurrentHighBoundaryD parameters L compact lower positive lowerHalf lengthPositive 0 0 state.outerInverseState field).val + knownBoundary.val) := by
  simp only [currentHighFormValue, currentHighBulkFormValue, actualCurrentHighBoundaryFormValue] at equation
  simp only [actualFullHighOutput, inner_add_right]
  linear_combination -equation

theorem actualFullHighOutput_zeroOuter
    (field test : annularEnergySpace lower L positive)
    (known : HighKnownSourceBulk lower) (auxiliary : HighAuxiliarySourceBulk lower)
    (knownBoundary : HighBoundaryPrimitive parameters 0 0)
    (equation : currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field test =
      inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test)
        (actualHighKnownBulkOutput parameters L compact lower positive (lowerHalf.trans (by norm_num)) state known auxiliary) -
      inner ℂ (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test) knownBoundary.val)
    (outerZero : actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test = 0) :
    inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test)
      (actualFullHighOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field known auxiliary) = 0 := by
  have pairing := actualFullHighOutput_variational parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    field test known auxiliary knownBoundary equation
  rw [outerZero, inner_zero_left] at pairing
  exact pairing

/-- The SAME constructed solution obeys the exact three-row weak pairing,
with the full physical affine outer flux on the right. Compact tests therefore
remove only the actual outer test trace. -/
theorem actualHighEnergySolution_full_packet
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)
    (known : HighKnownSourceBulk lower) (auxiliary : HighAuxiliarySourceBulk lower)
    (datum : HighBoundaryPrimitive parameters 0 0) (source : ZAmbient parameters 2)
    (innerValue : AnnularBoundary)
    (test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive) :
    let solution := actualHighEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      known auxiliary datum source innerValue
    inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test.val)
      (actualFullHighOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state solution known auxiliary) =
    inner ℂ (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test.val)
      ((actualCurrentHighBoundaryD parameters L compact lower positive lowerHalf lengthPositive 0 0 state.outerInverseState solution).val +
        (actualHighKnownBoundaryVector state.outerInverseState 0 0 datum source).val) := by
  dsimp only
  have equation := actualHighEnergySolution_complex parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    known auxiliary datum source innerValue test
  simp only [currentHighFormValue, currentHighBulkFormValue, actualCurrentHighBoundaryFormValue,
    actualHighKnownFunctionalValue] at equation
  simp only [actualFullHighOutput, inner_add_right]
  linear_combination -equation

end Grad.AnnularCurrentSolution
