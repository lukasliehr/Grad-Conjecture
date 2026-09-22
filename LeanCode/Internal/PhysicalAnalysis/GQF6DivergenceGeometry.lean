import GQF5RadialProjection

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.Ledger
open Grad.NonlinearRange Grad.NonlinearQuotientBounds

def planarDivJet (field : ClosedJet 3) : ClosedJet 1 :=
  valueMapJet (matrixUnit 0 0) (partialJet 0 field) +
    valueMapJet (matrixUnit 0 1) (partialJet 1 field)

theorem planarDivJet_value (field : ClosedJet 3) (point : ClosedDisk) :
    (planarDivJet field).value point 0 =
      (partialJet 0 field).value point 0 + (partialJet 1 field).value point 1 := by
  simp [planarDivJet, closedJet_value_add, valueMapJet_value, matrixUnit_apply, operatorBasis]

def complexCoordinate (coordinate : Fin 2) : SpatialPlane →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (coordinateLinear coordinate)

def complexComponent (coordinate : Fin 3) : ComplexEuclidean 3 →L[ℝ] ℂ :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 => ℂ) coordinate).restrictScalars ℝ

theorem complexCoordinate_apply (coordinate : Fin 2) (point : SpatialPlane) :
    complexCoordinate coordinate point = (point coordinate : ℂ) := rfl

theorem complexComponent_apply (coordinate : Fin 3) (value : ComplexEuclidean 3) :
    complexComponent coordinate value = value coordinate := rfl

theorem radialContraction_derivative_zero (field : ClosedJet 3)
    (radialZero : apProductJet radialRowJet field = 0) (point : ClosedDisk)
    (inside : point.val ∈ openUnitDisk) (direction : Fin 2) :
    (spatialBasis direction 0 : ℂ) * field.value point 0 +
      (point.val 0 : ℂ) * (partialJet direction field).value point 0 +
      ((spatialBasis direction 1 : ℂ) * field.value point 1 +
        (point.val 1 : ℂ) * (partialJet direction field).value point 1) = 0 := by
  let extension := smoothClosedExtension field
  have derivative := (smoothClosedExtension_smooth field).differentiable (by simp)
    |>.differentiableAt (x := point.val) |>.hasFDerivAt
  have first := ((complexCoordinate 0).hasFDerivAt (x := point.val)).mul
    ((complexComponent 0).hasFDerivAt.comp point.val derivative)
  have second := ((complexCoordinate 1).hasFDerivAt (x := point.val)).mul
    ((complexComponent 1).hasFDerivAt.comp point.val derivative)
  have total := first.add second
  have localZero : (fun source : SpatialPlane =>
      complexCoordinate 0 source * complexComponent 0 (smoothClosedExtension field source) +
      complexCoordinate 1 source * complexComponent 1 (smoothClosedExtension field source)) =ᶠ[𝓝 point.val]
        fun _ => (0 : ℂ) := by
    filter_upwards [openUnitDisk_isOpen.mem_nhds inside] with source member
    let closed : ClosedDisk := ⟨source, openDiskMembershipClosed source member⟩
    have zero := congrArg (fun jet : ClosedJet 1 => jet.value closed 0) radialZero
    rw [apProductJet_value, radialRowJet_value] at zero
    simp only [complexCoordinate_apply, complexComponent_apply]
    rw [show smoothClosedExtension field source = field.value closed from smoothClosedExtension_value field closed]
    exact zero
  have unique := total.unique ((hasFDerivAt_const (0 : ℂ) point.val).congr_of_eventuallyEq localZero)
  have value := congrArg (fun mapping : SpatialPlane →L[ℝ] ℂ => mapping (spatialBasis direction)) unique
  have partialLaw : (fderiv ℝ (smoothClosedExtension field) point.val) (spatialBasis direction) =
      (partialJet direction field).value point := by
    have law := partialJet_global_value (smoothClosedExtension field) (smoothClosedExtension_smooth field) direction point
    rw [smoothClosedExtension_restricts] at law
    exact law.symm
  simp only [add_apply, smul_apply, Function.comp_apply,
    ContinuousLinearMap.comp_apply, zero_apply,
    complexCoordinate_apply, complexComponent_apply, partialLaw, smoothClosedExtension_value,
    smul_eq_mul] at value
  linear_combination value

theorem planarDiv_complement_offAxis (field : ClosedJet 3) (point : ClosedDisk)
    (inside : point.val ∈ openUnitDisk) (nonzero : point.val ≠ 0) :
    (planarDivJet (fixedComplementJet field)).value point 0 = 0 := by
  let image := fixedComplementJet field
  have radialFirst := radialContraction_derivative_zero image
    (radialRowJet_complement_zero field) point inside 0
  have radialSecond := radialContraction_derivative_zero image
    (radialRowJet_complement_zero field) point inside 1
  simp [spatialBasis] at radialFirst radialSecond
  have rotation := rotationJet_fixedComplement field
  have rotationFirst := congrArg (fun jet : ClosedJet 3 => jet.value point 0) rotation
  have rotationSecond := congrArg (fun jet : ClosedJet 3 => jet.value point 1) rotation
  simp only [rotationJet, sub_eq_add_neg, closedJet_value_add, closedJet_value_neg,
    ContinuousMap.add_apply, ContinuousMap.neg_apply, coordinateJet_value, valueMapJet_value,
    PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply, Complex.real_smul] at rotationFirst rotationSecond
  change (point.val 0 : ℂ) * (partialJet 1 image).value point 0 -
      (point.val 1 : ℂ) * (partialJet 0 image).value point 0 =
        -image.value point 1 at rotationFirst
  change (point.val 0 : ℂ) * (partialJet 1 image).value point 1 -
      (point.val 1 : ℂ) * (partialJet 0 image).value point 1 =
        image.value point 0 at rotationSecond
  have first : (point.val 0 : ℂ) *
      ((partialJet 0 image).value point 0 + (partialJet 1 image).value point 1) = 0 := by
    linear_combination radialFirst + rotationSecond
  have second : (point.val 1 : ℂ) *
      ((partialJet 0 image).value point 0 + (partialJet 1 image).value point 1) = 0 := by
    linear_combination radialSecond - rotationFirst
  rw [planarDivJet_value]
  by_cases firstZero : point.val 0 = 0
  · have secondNonzero : point.val 1 ≠ 0 := by
      intro secondZero
      apply nonzero
      apply PiLp.ext
      intro coordinate
      fin_cases coordinate <;> assumption
    exact (mul_eq_zero.mp second).resolve_left (Complex.ofReal_ne_zero.mpr secondNonzero)
  · exact (mul_eq_zero.mp first).resolve_left (Complex.ofReal_ne_zero.mpr firstZero)

/-- Smooth divergence is zero on the full disk, including the axis and boundary.
The final extension uses faithful continuous L2 realization, not a polar quotient. -/
theorem planarDivJet_complement_zero (field : ClosedJet 3) :
    planarDivJet (fixedComplementJet field) = 0 := by
  apply closedJet_eq_of_value_eq
  apply closedContinuousToDiskL2_eq_zero
  apply Lp.ext
  have nonzero : ∀ᵐ point : SpatialPlane ∂volume.restrict openUnitDisk, point ≠ 0 := by
    simp only [ae_iff, not_not]
    change (volume.restrict openUnitDisk) {0} = 0
    exact measure_singleton 0
  filter_upwards [closedContinuousToDiskL2_ae (planarDivJet (fixedComplementJet field)).value,
    Lp.coeFn_zero (ComplexEuclidean 1) 2 (volume.restrict openUnitDisk),
    ae_restrict_mem openUnitDisk_isOpen.measurableSet, nonzero] with point value zero inside notZero
  rw [value, zero, closedDiskLift, dif_pos (openDiskMembershipClosed point inside)]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  exact planarDiv_complement_offAxis field ⟨point, openDiskMembershipClosed point inside⟩ inside notZero

end Grad.GaugeCoefficients.Physical.Compensated
