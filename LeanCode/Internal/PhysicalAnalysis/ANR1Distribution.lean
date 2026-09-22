import ANH19PhysicalConsumer

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory
open scoped ContDiff

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.CircularHighWeak
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- The literal scalar Cartesian test Laplacian, using the accepted ordered
weak derivative convention. -/
def testLaplacian (test : Grad.PDEBootstrap.Spatial → ℝ) : Grad.PDEBootstrap.Spatial → ℝ :=
  Grad.WeakTesting.orderedTestDerivative 2 (fun _ => 0) test +
    Grad.WeakTesting.orderedTestDerivative 2 (fun _ => 1) test

/-- Actual full-disk distributional Laplacian; no high restriction on tests. -/
def HasDiskWeakLaplacian (field laplacian : DiskL2 1) : Prop :=
  ∀ (vector : PhysicalValue 1) (test : Grad.PDEBootstrap.Spatial → ℝ),
    ContDiff ℝ ∞ test → HasCompactSupport test → tsupport test ⊆ openUnitDisk →
      (∫ point in openUnitDisk, test point • inner ℂ vector (laplacian point)) =
        ∫ point in openUnitDisk, testLaplacian test point • inner ℂ vector (field point)

theorem apDiskPairing_literal (vector : PhysicalValue 1)
    (test : Grad.PDEBootstrap.Spatial → ℝ) (smooth : ContDiff ℝ ∞ test)
    (compact : HasCompactSupport test) (field : DiskL2 1) :
    apDiskPairing 1 0 vector test smooth compact field =
      ∫ point in openUnitDisk, test point • inner ℂ vector (field point) := by
  rw [apDiskPairing, ContinuousLinearMap.comp_apply, Grad.WeakTesting.compactPairing_apply]
  apply integral_congr_ae
  filter_upwards [apDiskInjection_ae field] with point literal
  rw [literal]
  rfl

theorem apDiskDerivativePairing_literal (vector : PhysicalValue 1)
    (test : Grad.PDEBootstrap.Spatial → ℝ) (smooth : ContDiff ℝ ∞ test)
    (compact : HasCompactSupport test) (rank : ℕ) (word : CartesianWord rank)
    (field : DiskL2 1) :
    apDiskDerivativePairing 1 0 vector test smooth compact rank word field =
      ∫ point in openUnitDisk, Grad.WeakTesting.orderedTestDerivative rank word test point •
        inner ℂ vector (field point) := by
  rw [apDiskDerivativePairing, ContinuousLinearMap.comp_apply,
    Grad.WeakTesting.orderedDerivativePairing_apply]
  apply integral_congr_ae
  filter_upwards [apDiskInjection_ae field] with point literal
  rw [literal]
  rfl

/-- These are the actual AP1 weak first derivatives of every element of the
accepted disk H1 completion. -/
theorem diskGrade_weak (field : diskGrade) (index : Grad.GaugeCoefficients.Algebra.DerivativeIndex 1)
    (vector : PhysicalValue 1) (test : Grad.PDEBootstrap.Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    (supported : tsupport test ⊆ openUnitDisk) :
    apDiskPairing 1 0 vector test smooth compact (diskCoordinate index field) =
      (-1 : ℂ) ^ Grad.GaugeCoefficients.Algebra.derivativeOrder index *
        apDiskDerivativePairing 1 0 vector test smooth compact
          (Grad.GaugeCoefficients.Algebra.derivativeOrder index) (apIndexWord index) (diskBulk field) :=
  apCompleted_weak 1 0 0 1 0 index field.val 0 vector test smooth compact supported

theorem diskGradX_weak (field : diskGrade) (vector : PhysicalValue 1)
    (test : Grad.PDEBootstrap.Spatial → ℝ) (smooth : ContDiff ℝ ∞ test)
    (compact : HasCompactSupport test) (supported : tsupport test ⊆ openUnitDisk) :
    apDiskPairing 1 0 vector test smooth compact (diskGradX field) =
      -apDiskDerivativePairing 1 0 vector test smooth compact 1 (fun _ => 0) (diskBulk field) := by
  have identity := diskGrade_weak field diskXIndex vector test smooth compact supported
  have word : apIndexWord diskXIndex = fun _ => 0 := by funext position; fin_cases position; rfl
  exact identity.trans ((congrArg
    (fun selected : CartesianWord 1 => (-1 : ℂ) ^ 1 *
      apDiskDerivativePairing 1 0 vector test smooth compact 1 selected (diskBulk field)) word).trans
        ((congrArg (fun factor : ℂ => factor * _) (pow_one (-1 : ℂ))).trans (neg_one_mul _)))

theorem diskGradY_weak (field : diskGrade) (vector : PhysicalValue 1)
    (test : Grad.PDEBootstrap.Spatial → ℝ) (smooth : ContDiff ℝ ∞ test)
    (compact : HasCompactSupport test) (supported : tsupport test ⊆ openUnitDisk) :
    apDiskPairing 1 0 vector test smooth compact (diskGradY field) =
      -apDiskDerivativePairing 1 0 vector test smooth compact 1 (fun _ => 1) (diskBulk field) := by
  have identity := diskGrade_weak field diskYIndex vector test smooth compact supported
  have word : apIndexWord diskYIndex = fun _ => 1 := by funext position; fin_cases position; rfl
  exact identity.trans ((congrArg
    (fun selected : CartesianWord 1 => (-1 : ℂ) ^ 1 *
      apDiskDerivativePairing 1 0 vector test smooth compact 1 selected (diskBulk field)) word).trans
        ((congrArg (fun factor : ℂ => factor * _) (pow_one (-1 : ℂ))).trans (neg_one_mul _)))

end Grad.CircularHighRegularity
