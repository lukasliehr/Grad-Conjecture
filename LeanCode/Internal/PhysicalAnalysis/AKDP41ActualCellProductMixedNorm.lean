import AKDP40ActualMixedOrderInputNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set Filter MeasureTheory
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap
open Grad.ActualOriginalSourceFirst Grad.OriginalCartesianTameEstimate
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.SourceCollarCoefficients

theorem startupOriginalNaturalDerivative_same {dimension : ℕ}
    (parameters : PhaseParameters) (core : ACore parameters dimension)
    (rank moment : ℕ) (word : CartesianWord rank) :
    ∀ᵐ point ∂volume.restrict openUnitDisk,∀ cell : ℤ,
      originalMixedDerivativeCarrier parameters (unitDiskAdmissible parameters) core rank moment word point cell =
        (cellFrequency cell : ℂ)^moment • originalSourceOrderedJoint parameters core rank word point cell := by
  apply ae_all_iff.mpr
  intro cell
  have same : fieldCellProjection dimension openUnitDisk cell
      (originalMixedDerivativeCarrier parameters (unitDiskAdmissible parameters) core rank moment word) =
      (cellFrequency cell : ℂ)^moment • fieldCellProjection dimension openUnitDisk cell
        (originalSourceOrderedJoint parameters core rank word) := by
    rw [originalMixedDerivativeCarrier_coordinate,originalSourceOrderedJoint_coordinate]
    simp only [originalMixedDerivativeCoordinate,originalSourceOrderedCoordinate,unit_scaledCellWeight]
  filter_upwards [fieldCellProjection_ae dimension openUnitDisk
      (originalMixedDerivativeCarrier parameters (unitDiskAdmissible parameters) core rank moment word),
    fieldCellProjection_ae dimension openUnitDisk (originalSourceOrderedJoint parameters core rank word),
    Lp.coeFn_smul ((cellFrequency cell : ℂ)^moment)
      (fieldCellProjection dimension openUnitDisk cell (originalSourceOrderedJoint parameters core rank word))]
    with point projected original scaled
  have equality := congrArg (fun field : DiskL2 dimension => field point) same
  rw [projected cell,scaled] at equality
  simp only [Pi.smul_apply] at equality
  rw [original cell] at equality
  exact equality

/-- A genuine cell-dependent product pays exactly its cell-power cost
and the remaining spatial order. This is the phase allocation before
the original adjustable mixed-order endpoint is applied. -/
theorem startupActualCellProduct_mixedNorm {dimension : ℕ}
    (parameters : PhaseParameters) (core : ACore parameters dimension)
    (grade rank moment : ℕ) (allocated : rank+moment≤grade) (word : CartesianWord rank)
    (coefficient : ℤ → Spatial → ℝ) (constant : ℝ) (nonnegative : 0≤constant)
    (bounded : ∀ cell point,|coefficient cell point|≤constant*cellFrequency cell^moment)
    (measurable : ∀ cell,AEStronglyMeasurable (coefficient cell) (volume.restrict openUnitDisk))
    (product : StartupL2 dimension)
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk,∀ cell : ℤ,
      product point cell=(coefficient cell point : ℂ) • originalSourceOrderedJoint parameters core rank word point cell) :
    ‖product‖≤constant*originalMixedOrderNorm parameters grade rank core := by
  let normalized := fun cell point => coefficient cell point / cellFrequency cell^moment
  have normalizedBound (cell : ℤ) (point : Spatial) : |normalized cell point|≤constant := by
    change |coefficient cell point / cellFrequency cell^moment|≤constant
    rw [abs_div,abs_of_pos (pow_pos (cellFrequency_pos cell) _)]
    exact (div_le_iff₀ (pow_pos (cellFrequency_pos cell) _)).mpr (bounded cell point)
  have normalizedMeasurable (cell : ℤ) : AEStronglyMeasurable (normalized cell) (volume.restrict openUnitDisk) := by
    change AEStronglyMeasurable (fun point => coefficient cell point / cellFrequency cell^moment) _
    simp only [div_eq_mul_inv]
    exact (measurable cell).mul aestronglyMeasurable_const
  let carrier := originalMixedDerivativeCarrier parameters (unitDiskAdmissible parameters) core rank moment word
  have productSame : product=startupMomentDiagonalField normalized constant nonnegative normalizedBound normalizedMeasurable carrier := by
    apply Lp.ext
    filter_upwards [same,startupMomentDiagonalField_ae normalized constant nonnegative normalizedBound normalizedMeasurable carrier,
      startupOriginalNaturalDerivative_same parameters core rank moment word] with point productValue diagonalValue carrierValue
    apply lp.ext
    funext cell
    rw [productValue cell,diagonalValue cell,carrierValue cell,smul_smul]
    congr 1
    change (coefficient cell point : ℂ)=((coefficient cell point / cellFrequency cell^moment : ℝ) : ℂ)*
      (cellFrequency cell : ℂ)^moment
    rw [← Complex.ofReal_pow,← Complex.ofReal_mul,div_mul_cancel₀ _ (pow_ne_zero _ (cellFrequency_pos cell).ne')]
  rw [productSame]
  exact (startupMomentDiagonalField_norm normalized constant nonnegative normalizedBound normalizedMeasurable carrier).trans
    (mul_le_mul_of_nonneg_left (startupOriginalNaturalDerivative_mixedNorm parameters core grade rank moment allocated word) nonnegative)

end Grad.CartesianStartup
