import AIA9ExactCircularOutputRepresentatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCircularForm
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularCurrentEnergy Grad.AnnularVariational
open Grad.AnnularTiltedReference Grad.AnnularKernelL2

variable (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))

/-- Exact equality of completed operators on the actual physical homogeneous packet. -/
theorem circularEliminatedBulkAction_packet (power : ℕ) (field : annularEnergySpace lower L positive) :
    circularEliminatedBulkAction parameters L lower positive bounded power
      (highEightEnergyPacket parameters lower L positive lengthPositive widthHalf widthLength field) =
    highBulkSlot lower (0 : Fin 3) (circularHighX parameters lower L positive lengthPositive widthHalf widthLength field) +
      highBulkSlot lower (1 : Fin 3) (circularHighC lower L positive field) +
      highBulkSlot lower (2 : Fin 3) (circularHighRV parameters lower L positive lengthPositive widthHalf widthLength field) := by
  apply lp.ext
  funext mode
  by_cases high : 3 ≤ |mode.1|
  · let index : HighAnnularMode := ⟨mode, high⟩
    apply Lp.ext
    filter_upwards [circularEliminatedBulkAction_packet_ae parameters L lower positive bounded power lengthPositive widthHalf widthLength field,
      circularHighCoordinates_ae parameters lower L positive lengthPositive widthHalf widthLength field,
      highThreePacket_ae lower (circularHighX parameters lower L positive lengthPositive widthHalf widthLength field)
        (circularHighC lower L positive field) (circularHighRV parameters lower L positive lengthPositive widthHalf widthLength field)]
      with radius actual coordinates output
    rw [actual index, output index]
    rcases coordinates index with ⟨x, c, rv⟩
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate
    · exact x.symm
    · exact c.symm
    · exact (rv.trans (congrArg (fun scalar =>
        -highEnergyAngularRadius lower L positive (bEnergyDecode lower L positive field) index radius 0 -
          2 * Grad.BoundaryKernelAction.angularInverseMultiplier index.val * scalar) x)).symm
  · have leftZero := circularEliminatedBulkAction_low parameters L lower positive bounded power
      (highEightEnergyPacket parameters lower L positive lengthPositive widthHalf widthLength field) mode high
    have firstZero := highBulkSlot_low lower (0 : Fin 3)
      (circularHighX parameters lower L positive lengthPositive widthHalf widthLength field) mode high
    have secondZero := highBulkSlot_low lower (1 : Fin 3) (circularHighC lower L positive field) mode high
    have thirdZero := highBulkSlot_low lower (2 : Fin 3)
      (circularHighRV parameters lower L positive lengthPositive widthHalf widthLength field) mode high
    have sumZero := congrArg₂ (· + ·) (congrArg₂ (· + ·) firstZero secondZero) thirdZero
    simp only [zero_add] at sumZero
    exact leftZero.trans sumZero.symm

/-- Literal three-factor pairing of the completed circular physical output. -/
theorem circularHighBulkFormValue_coordinates (power : ℕ) (field test : annularEnergySpace lower L positive) :
    circularHighBulkFormValue parameters L lower positive bounded lengthPositive widthHalf widthLength power field test =
      -(inner ℂ (highPhysicalTestDerivative parameters lower L positive lengthPositive widthHalf widthLength test)
          (circularHighX parameters lower L positive lengthPositive widthHalf widthLength field) +
        inner ℂ (highEnergyCell lower L positive (bEnergyDecode lower L positive test)) (circularHighC lower L positive field) +
        inner ℂ (highEnergyAngularRadius lower L positive (bEnergyDecode lower L positive test))
          (circularHighRV parameters lower L positive lengthPositive widthHalf widthLength field)) := by
  unfold circularHighBulkFormValue
  rw [circularEliminatedBulkAction_packet]
  change -inner ℂ
    (highBulkSlot lower (0 : Fin 3) _ + highBulkSlot lower (1 : Fin 3) _ + highBulkSlot lower (2 : Fin 3) _) _ = _
  rw [highThreePacket_inner]
  rfl

end Grad.AnnularCircularForm
