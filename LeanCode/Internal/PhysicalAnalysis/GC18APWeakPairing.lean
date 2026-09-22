import GC18APProjection
import WTCProof

noncomputable section

set_option maxHeartbeats 1000000

open MeasureTheory
open scoped ContDiff

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers

def apDiskInjection (dimension : ℕ) : DiskL2 dimension →L[ℂ] FieldL2 dimension openUnitDisk :=
  (cellSingle (PhysicalValue dimension) 0).compLpL 2 (volume.restrict openUnitDisk)

theorem apDiskInjection_ae {dimension : ℕ} (field : DiskL2 dimension) :
    ∀ᵐ point ∂volume.restrict openUnitDisk,
      apDiskInjection dimension field point = cellSingle (PhysicalValue dimension) 0 (field point) :=
  (cellSingle (PhysicalValue dimension) 0).coeFn_compLp field

theorem apDiskInjection_injective (dimension : ℕ) : Function.Injective (apDiskInjection dimension) := by
  intro first second equality
  apply Lp.ext
  filter_upwards [apDiskInjection_ae first, apDiskInjection_ae second] with point firstValue secondValue
  rw [equality, secondValue] at firstValue
  have coordinate := congrArg (fun values : CellValues dimension => values 0) firstValue
  simpa only [cellSingle, lp.singleContinuousLinearMap_apply, lp.single_apply, Pi.single_eq_same] using coordinate.symm

def apTestValue (dimension : ℕ) (cell : ℤ) (vector : PhysicalValue dimension) : PhysicalValue dimension →L[ℂ] ℂ :=
  (innerSL ℂ vector).comp ((cellProjection (PhysicalValue dimension) cell).comp (cellSingle (PhysicalValue dimension) 0))

def apDiskPairing (dimension : ℕ) (cell : ℤ) (vector : PhysicalValue dimension)
    (test : Grad.PDEBootstrap.Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    DiskL2 dimension →L[ℂ] ℂ :=
  (Grad.WeakTesting.compactPairing dimension openUnitDisk cell vector test smooth compact).comp (apDiskInjection dimension)

def apDiskDerivativePairing (dimension : ℕ) (cell : ℤ) (vector : PhysicalValue dimension)
    (test : Grad.PDEBootstrap.Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    (rank : ℕ) (word : CartesianWord rank) : DiskL2 dimension →L[ℂ] ℂ :=
  (Grad.WeakTesting.orderedDerivativePairing dimension openUnitDisk cell vector test smooth compact rank word).comp (apDiskInjection dimension)

theorem apDiskPairing_closed {dimension : ℕ} (cell : ℤ) (vector : PhysicalValue dimension)
    (test : Grad.PDEBootstrap.Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    (field : C(ClosedDisk, ComplexEuclidean dimension)) :
    apDiskPairing dimension cell vector test smooth compact (closedContinuousToDiskL2 field) =
      ∫ point in openUnitDisk, test point • apTestValue dimension cell vector (closedDiskLift field point) := by
  rw [apDiskPairing, ContinuousLinearMap.comp_apply, Grad.WeakTesting.compactPairing_apply]
  apply integral_congr_ae
  filter_upwards [apDiskInjection_ae (closedContinuousToDiskL2 field), closedContinuousToDiskL2_ae field]
    with point injection value
  rw [injection, value]
  rfl

theorem apDiskDerivativePairing_closed {dimension : ℕ} (cell : ℤ) (vector : PhysicalValue dimension)
    (test : Grad.PDEBootstrap.Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    (rank : ℕ) (word : CartesianWord rank) (field : C(ClosedDisk, ComplexEuclidean dimension)) :
    apDiskDerivativePairing dimension cell vector test smooth compact rank word (closedContinuousToDiskL2 field) =
      ∫ point in openUnitDisk, Grad.WeakTesting.orderedTestDerivative rank word test point •
        apTestValue dimension cell vector (closedDiskLift field point) := by
  rw [apDiskDerivativePairing, ContinuousLinearMap.comp_apply, Grad.WeakTesting.orderedDerivativePairing_apply]
  apply integral_congr_ae
  filter_upwards [apDiskInjection_ae (closedContinuousToDiskL2 field), closedContinuousToDiskL2_ae field]
    with point injection value
  rw [injection, value]
  rfl

theorem apDiskPairing_separates {dimension : ℕ} (first second : DiskL2 dimension)
    (equalities : ∀ (cell : ℤ) (vector : PhysicalValue dimension) (test : Grad.PDEBootstrap.Spatial → ℝ)
      (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test), tsupport test ⊆ openUnitDisk →
      apDiskPairing dimension cell vector test smooth compact first = apDiskPairing dimension cell vector test smooth compact second) :
    first = second := by
  apply apDiskInjection_injective
  apply Grad.WeakTesting.Separation.equality dimension openUnitDisk openUnitDisk_isOpen
  exact equalities

end Grad.GaugeCoefficients.Physical.RadialLedger
