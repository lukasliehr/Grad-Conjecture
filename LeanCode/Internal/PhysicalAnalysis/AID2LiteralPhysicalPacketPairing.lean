import AID1ActualHighOutputCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentGreen
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularCircularForm
open Grad.GaugeCoefficients.Physical.Ledger

/-- Actual scalar inclusion and extraction are adjoint on the radial L2 carrier. -/
theorem radialPhysicalSlot_pairing {dimension : ℕ} (lower : ℝ) (slot : Fin dimension)
    (test : RadialL2 1 lower) (field : RadialL2 dimension lower) :
    inner ℂ (radialMatrixUnit lower slot 0 test) field =
      inner ℂ test (radialMatrixUnit lower 0 slot field) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [radialMatrixUnit_ae lower slot 0 test, radialMatrixUnit_ae lower (0 : Fin 1) slot field]
    with radius testLaw fieldLaw
  rw [testLaw, fieldLaw]
  simp [PiLp.inner_apply, operatorBasis, apply_ite]

theorem bulkPhysicalSlot_pairing {dimension : ℕ} (lower : ℝ) (slot : Fin dimension)
    (test : DivisionRow 1 lower) (field : DivisionRow dimension lower) :
    inner ℂ (bulkMatrixUnit lower slot 0 test) field =
      inner ℂ test (bulkMatrixUnit lower 0 slot field) := by
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro mode
  exact radialPhysicalSlot_pairing lower slot (test mode) (field mode)

/-- The actual high inclusion pairs with literal restriction of full output coefficients. -/
theorem highFullRestriction_pairing (lower : ℝ) (test : AnnularBulk lower) (field : DivisionRow 1 lower) :
    inner ℂ (highBulkIntoFull lower test) field = inner ℂ test (highFullRestriction lower field) := by
  simp only [lp.inner_eq_tsum]
  have support : Function.support (fun mode => inner ℂ (highBulkIntoFull lower test mode) (field mode)) ⊆
      {mode : ℤ × ℤ | 3 ≤ |mode.1|} := by
    intro mode member
    by_contra low
    apply member
    change inner ℂ (highBulkIntoFull lower test mode) (field mode) = 0
    rw [highBulkIntoFull_low lower test mode low, inner_zero_left]
  have equality := tsum_subtype_eq_of_support_subset support
  change (∑' mode : HighAnnularMode, inner ℂ (highBulkIntoFull lower test mode.val) (field mode.val)) = _ at equality
  simpa only [highBulkIntoFull_high, highFullRestriction_apply] using equality.symm

theorem highPhysicalOutput_pairing {dimension : ℕ} (lower : ℝ) (slot : Fin dimension)
    (test : AnnularBulk lower) (field : DivisionRow dimension lower) :
    inner ℂ (highBulkSlot lower slot test) field = inner ℂ test (highPhysicalOutput lower slot field) := by
  change inner ℂ (bulkMatrixUnit lower slot 0 (highBulkIntoFull lower test)) field = _
  rw [bulkPhysicalSlot_pairing, highFullRestriction_pairing]
  rfl

/-- Exact actual test packet pairing with arbitrary completed physical fluxes. -/
theorem physicalTestPacket_pairing (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (test : annularEnergySpace lower L positive) (field : DivisionRow 3 lower) :
    inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test) field =
      inner ℂ (highPhysicalTestDerivative parameters lower L positive lengthPositive widthHalf widthLength test)
        (highPhysicalOutput lower 0 field) +
      inner ℂ (highEnergyCell lower L positive (Grad.AnnularTiltedReference.bEnergyDecode lower L positive test))
        (highPhysicalOutput lower 1 field) +
      inner ℂ (highEnergyAngularRadius lower L positive (Grad.AnnularTiltedReference.bEnergyDecode lower L positive test))
        (highPhysicalOutput lower 2 field) := by
  change inner ℂ (highBulkSlot lower (0 : Fin 3) _ + highBulkSlot lower (1 : Fin 3) _ + highBulkSlot lower (2 : Fin 3) _) field = _
  rw [inner_add_left, inner_add_left, highPhysicalOutput_pairing, highPhysicalOutput_pairing, highPhysicalOutput_pairing]
  rfl

end Grad.AnnularCurrentGreen
