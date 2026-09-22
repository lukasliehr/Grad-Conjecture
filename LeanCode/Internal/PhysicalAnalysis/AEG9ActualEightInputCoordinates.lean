import AEG8ActualErrorTestPairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentEnergy
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularTiltedReference Grad.AnnularKernelL2
open Grad.GaugeCoefficients.Physical.Ledger Grad.BoundaryKernelAction

section Packet
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

/-- The actual completed eight-slot packet has exactly the stated physical
unknowns and zero known source coordinates, coefficient by coefficient. -/
theorem highEightEnergyPacket_ae (field : annularEnergySpace lower length positive) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : HighAnnularMode,
      highEightEnergyPacket parameters lower length positive lengthPositive widthHalf widthLength field mode.val radius =
        (highPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength field mode radius 0) • operatorBasis 0 +
        (highEnergyAngularRadius lower length positive (bEnergyDecode lower length positive field) mode radius 0) • operatorBasis 1 +
        ((length : ℂ) * highEnergyCell lower length positive (bEnergyDecode lower length positive field) mode radius 0) • operatorBasis 2 +
        (highEnergyRadius lower length positive (bEnergyDecode lower length positive field) mode radius 0) • operatorBasis 3 := by
  rw [ae_all_iff]
  intro mode
  let decoded := bEnergyDecode lower length positive field
  let first : DivisionRow 8 lower := highBulkSlot lower 0
    (highPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength field)
  let second : DivisionRow 8 lower := highBulkSlot lower 1 (highEnergyAngularRadius lower length positive decoded)
  let third : DivisionRow 8 lower := highBulkSlot lower 2 ((length : ℂ) • highEnergyCell lower length positive decoded)
  let fourth : DivisionRow 8 lower := highBulkSlot lower 3 (highEnergyRadius lower length positive decoded)
  have exactSum : highEightEnergyPacket parameters lower length positive lengthPositive widthHalf widthLength field =
      first + second + third + fourth := rfl
  rw [exactSum]
  filter_upwards [highBulkSlot_ae lower (0 : Fin 8)
      (highPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength field),
    highBulkSlot_ae lower (1 : Fin 8) (highEnergyAngularRadius lower length positive decoded),
    highBulkSlot_ae lower (2 : Fin 8) ((length : ℂ) • highEnergyCell lower length positive decoded),
    highBulkSlot_ae lower (3 : Fin 8) (highEnergyRadius lower length positive decoded),
    Lp.coeFn_add (first mode.val) (second mode.val),
    Lp.coeFn_add (first mode.val + second mode.val) (third mode.val),
    Lp.coeFn_add (first mode.val + second mode.val + third mode.val) (fourth mode.val),
    Lp.coeFn_smul (length : ℂ) (highEnergyCell lower length positive decoded mode)]
      with radius one two three four sum12 sum123 sum1234 cell
  change ((first mode.val + second mode.val) + third mode.val + fourth mode.val) radius = _
  have h12 : (first mode.val + second mode.val) radius =
      first mode.val radius + second mode.val radius := sum12
  have h123 : (first mode.val + second mode.val + third mode.val) radius =
      (first mode.val + second mode.val) radius + third mode.val radius := sum123
  have h1234 : (first mode.val + second mode.val + third mode.val + fourth mode.val) radius =
      (first mode.val + second mode.val + third mode.val) radius + fourth mode.val radius := sum1234
  have hcell : ((length : ℂ) • highEnergyCell lower length positive decoded mode) radius 0 =
      (length : ℂ) * highEnergyCell lower length positive decoded mode radius 0 :=
    congrArg (fun v : ComplexEuclidean 1 => v 0) cell
  have hthird := (three mode).trans (congrArg
    (fun value : ℂ => value • (operatorBasis (2 : Fin 8))) hcell)
  exact h1234.trans ((congrArg₂ (fun a b : ComplexEuclidean 8 => a + b)
    (h123.trans (congrArg₂ (fun a b : ComplexEuclidean 8 => a + b)
      (h12.trans (congrArg₂ (fun a b : ComplexEuclidean 8 => a + b) (one mode) (two mode)))
      hthird)) (four mode)))


end Packet
end Grad.AnnularCurrentEnergy
