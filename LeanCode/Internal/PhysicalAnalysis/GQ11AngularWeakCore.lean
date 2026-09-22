import GQ10CompletedQuarter

noncomputable section

set_option maxHeartbeats 1600000

open scoped ContDiff

namespace Grad.GaugeCoefficients.Physical.GaugeTransfer

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearRange Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GenericCarriers
open Grad.NonlinearProduct Grad.NonlinearQuotientBounds

theorem partialJet_coordinate_cross {dimension : ℕ} (field : ClosedJet dimension)
    (direction coordinate : Fin 2) (different : direction ≠ coordinate) :
    partialJet direction (coordinateJet coordinate field) = coordinateJet coordinate (partialJet direction field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [partialJet_value, coordinateJet_value, partialJet_value]
  unfold coordinateJet
  rw [smoothScalar_partial_value]
  have derivativeZero : spatialPartial direction (coordinateLinear coordinate) point.val = 0 := by
    unfold spatialPartial
    rw [(coordinateLinear coordinate).fderiv]
    change spatialBasis direction coordinate = 0
    unfold spatialBasis
    exact Pi.single_eq_of_ne (fun equality => different equality.symm) 1
  rw [derivativeZero, zero_smul, zero_add]
  rfl

def diskCoordinateCoefficient (dimension : ℕ) (coordinate : Fin 2) :
    C(ClosedDisk, ComplexEuclidean dimension →L[ℂ] ComplexEuclidean dimension) :=
  ⟨fun point => point.val coordinate • ContinuousLinearMap.id ℂ _, by fun_prop⟩

def diskCoordinateAction (dimension : ℕ) (coordinate : Fin 2) : DiskL2 dimension →L[ℂ] DiskL2 dimension :=
  closedOperatorL2 (diskCoordinateCoefficient dimension coordinate)

theorem diskCoordinateAction_core {dimension : ℕ} (coordinate : Fin 2) (field : ClosedJet dimension) :
    diskCoordinateAction dimension coordinate (closedContinuousToDiskL2 field.value) =
      closedContinuousToDiskL2 (coordinateJet coordinate field).value := by
  rw [diskCoordinateAction, closedOperatorL2_closed]
  apply congrArg closedContinuousToDiskL2
  apply ContinuousMap.ext
  intro point
  rfl

/-- The true formal adjoint test of -Y2*d1+Y1*d2, written in divergence
form. Its two coordinate derivatives have zero divergence. -/
def angularWeakPairing (dimension : ℕ) (cell : ℤ) (vector : PhysicalValue dimension)
    (test : Grad.PDEBootstrap.Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    DiskL2 dimension →L[ℂ] ℂ :=
  -((apDiskDerivativePairing dimension cell vector test smooth compact 1 (fun _ => 1)).comp (diskCoordinateAction dimension 0)) +
    ((apDiskDerivativePairing dimension cell vector test smooth compact 1 (fun _ => 0)).comp (diskCoordinateAction dimension 1))

theorem rotationJet_weak {dimension : ℕ} (field : ClosedJet dimension)
    (cell : ℤ) (vector : PhysicalValue dimension) (test : Grad.PDEBootstrap.Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) (supported : tsupport test ⊆ openUnitDisk) :
    apDiskPairing dimension cell vector test smooth compact (closedContinuousToDiskL2 (rotationJet field).value) =
      angularWeakPairing dimension cell vector test smooth compact (closedContinuousToDiskL2 field.value) := by
  have divergence : rotationJet field = partialJet 1 (coordinateJet 0 field) - partialJet 0 (coordinateJet 1 field) := by
    rw [partialJet_coordinate_cross field 1 0 (by decide), partialJet_coordinate_cross field 0 1 (by decide)]
    rfl
  rw [divergence, sub_eq_add_neg, closedJet_value_add, closedJet_value_neg,
    closedContinuousToDiskL2_add]
  have negative (value : C(ClosedDisk, ComplexEuclidean dimension)) :
      closedContinuousToDiskL2 (-value) = -closedContinuousToDiskL2 value := by
    rw [← neg_one_smul ℂ value, closedContinuousToDiskL2_smul, neg_one_smul]
  rw [negative, map_add, map_neg]
  have first := apClosedJet_weak (coordinateJet 0 field) (fun _ : Fin 1 => (1 : Fin 2)) cell vector test smooth compact supported
  have second := apClosedJet_weak (coordinateJet 1 field) (fun _ : Fin 1 => (0 : Fin 2)) cell vector test smooth compact supported
  change apDiskPairing dimension cell vector test smooth compact (closedContinuousToDiskL2 (partialJet 1 (coordinateJet 0 field)).value) = _ at first
  change apDiskPairing dimension cell vector test smooth compact (closedContinuousToDiskL2 (partialJet 0 (coordinateJet 1 field)).value) = _ at second
  rw [first, second]
  change _ = -apDiskDerivativePairing dimension cell vector test smooth compact 1 (fun _ => 1)
      (diskCoordinateAction dimension 0 (closedContinuousToDiskL2 field.value)) +
    apDiskDerivativePairing dimension cell vector test smooth compact 1 (fun _ => 0)
      (diskCoordinateAction dimension 1 (closedContinuousToDiskL2 field.value))
  rw [diskCoordinateAction_core, diskCoordinateAction_core]
  simp only [pow_one, neg_one_mul, neg_neg]

end Grad.GaugeCoefficients.Physical.GaugeTransfer
