import AEG6OriginalTiltedBulkFidelity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentEnergy
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularTiltedReference Grad.AnnularKernelL2

/-- Actual homogeneous normalized seven inputs for reconstruction. The flux
coordinate remains independent until the current first row is eliminated. -/
def highSevenEnergyPacket (lower length : ℝ) (positive : 0 < lower) :
    (DivisionRow 1 lower × annularEnergySpace lower length positive) →L[ℂ] DivisionRow 7 lower :=
  (bulkMatrixUnit lower 0 0).comp (ContinuousLinearMap.fst ℂ _ _) +
  (highBulkSlot lower 1).comp (((highEnergyAngularRadius lower length positive).comp
    (bEnergyDecode lower length positive)).comp (ContinuousLinearMap.snd ℂ _ _)) +
  (highBulkSlot lower 2).comp ((((length : ℂ) • highEnergyCell lower length positive).comp
    (bEnergyDecode lower length positive)).comp (ContinuousLinearMap.snd ℂ _ _)) +
  (highBulkSlot lower 3).comp (((highEnergyRadius lower length positive).comp
    (bEnergyDecode lower length positive)).comp (ContinuousLinearMap.snd ℂ _ _))

theorem highSevenEnergyPacket_bound (lower length : ℝ) (positive : 0 < lower)
    (flux : DivisionRow 1 lower) (field : annularEnergySpace lower length positive) :
    ‖highSevenEnergyPacket lower length positive (flux, field)‖ ≤
      ‖flux‖ + (2 + 2 * |length|) * ‖field‖ := by
  let decoded := bEnergyDecode lower length positive field
  have decodeBound : ‖decoded‖ ≤ ‖field‖ := physicalEnergyDecode_bound lower length positive field
  have first := bulkMatrixUnit_bound lower (0 : Fin 7) (0 : Fin 1) flux
  have second := (highBulkSlot_bound lower (1 : Fin 7) (highEnergyAngularRadius lower length positive decoded)).trans
    ((highEnergyAngularRadius_bound lower length positive decoded).trans decodeBound)
  have third := highBulkSlot_bound lower (2 : Fin 7) ((length : ℂ) • highEnergyCell lower length positive decoded)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs] at third
  have cell := (highEnergyCell_bound lower length positive decoded).trans
    (mul_le_mul_of_nonneg_left decodeBound (by norm_num : (0 : ℝ) ≤ 2))
  have thirdBound := third.trans (mul_le_mul_of_nonneg_left cell (abs_nonneg length))
  have fourth := (highBulkSlot_bound lower (3 : Fin 7) (highEnergyRadius lower length positive decoded)).trans
    ((highEnergyRadius_bound lower length positive decoded).trans
      (mul_le_mul_of_nonneg_left decodeBound (by norm_num : (0 : ℝ) ≤ 1 / 3)))
  calc
    _ ≤ ‖bulkMatrixUnit lower (0 : Fin 7) (0 : Fin 1) flux‖ +
      ‖highBulkSlot lower (1 : Fin 7) (highEnergyAngularRadius lower length positive decoded)‖ +
      ‖highBulkSlot lower (2 : Fin 7) ((length : ℂ) • highEnergyCell lower length positive decoded)‖ +
      ‖highBulkSlot lower (3 : Fin 7) (highEnergyRadius lower length positive decoded)‖ :=
        (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ ‖flux‖ + ‖field‖ + |length| * (2 * ‖field‖) + (1 / 3 : ℝ) * ‖field‖ :=
      add_le_add (add_le_add (add_le_add first second) thirdBound) fourth
    _ ≤ ‖flux‖ + (2 + 2 * |length|) * ‖field‖ := by nlinarith [norm_nonneg field]

/-- The actual AHU reconstruction errors act on this physical energy packet.
The coefficient constant is chosen before the collar and original physical state. -/
theorem highSevenEnergyPacket_actualError_bound (parameters : PhaseParameters) (L compact : ℝ) (power : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
        (state : AnnularReconstructionState parameters L compact) (flux : DivisionRow 1 lower)
        (field : annularEnergySpace lower L positive),
      ‖normalizedCovariantErrorAction parameters L compact lower positive bounded state power
          (highSevenEnergyPacket lower L positive (flux, field))‖ +
        ‖normalizedRotatedErrorAction parameters L compact lower positive bounded state power
          (highSevenEnergyPacket lower L positive (flux, field))‖ ≤
        constant * state.errorBudget power * (‖flux‖ + (2 + 2 * |L|) * ‖field‖) := by
  obtain ⟨constant, nonnegative, estimate⟩ := normalizedCompletedErrors_uniform parameters L compact power
  refine ⟨constant, nonnegative, ?_⟩
  intro lower positive bounded state flux field
  apply (estimate lower positive bounded state (highSevenEnergyPacket lower L positive (flux, field))).trans
  exact mul_le_mul_of_nonneg_left (highSevenEnergyPacket_bound lower L positive flux field)
    (mul_nonneg nonnegative
      (Grad.GaugeCoefficients.Physical.Allocation.physicalBudget_nonnegative parameters state.val.field
        state.val.rho state.val.epsilon _))

end Grad.AnnularCurrentEnergy
