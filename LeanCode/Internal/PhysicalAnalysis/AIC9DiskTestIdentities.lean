import AIC8CutoffIntegral
import ANR1Distribution

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace Grad.InteriorLocalization
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.WeightedJets.SpatialMultiplier

theorem firstTestDerivative_ordered (direction : Fin 2) (test : Spatial → ℝ) :
    firstTestDerivative direction test = Grad.WeakTesting.orderedTestDerivative 1 (fun _ => direction) test := by
  fin_cases direction
  · change scalarDerivative (1, 0) test = _
    unfold scalarDerivative
    congr 1
    funext position
    fin_cases position
    rfl
  · rfl

theorem secondTestDerivative_ordered (direction : Fin 2) (test : Spatial → ℝ) :
    secondTestDerivative direction test = Grad.WeakTesting.orderedTestDerivative 2 (fun _ => direction) test := by
  fin_cases direction
  · change scalarDerivative (2, 0) test = _
    unfold scalarDerivative
    congr 1
    funext position
    fin_cases position <;> rfl
  · rfl

theorem testLaplacian_second (test : Spatial → ℝ) :
    testLaplacian test = secondTestDerivative 0 test + secondTestDerivative 1 test := by
  rw [secondTestDerivative_ordered, secondTestDerivative_ordered]
  rfl

def diskGradient (direction : Fin 2) : diskGrade →L[ℂ] DiskL2 1 :=
  if direction = 0 then diskGradX else diskGradY

theorem diskGradient_weak (direction : Fin 2) (field : diskGrade) (vector : PhysicalValue 1)
    (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    (supported : tsupport test ⊆ openUnitDisk) :
    diskIntegral (diskGradient direction field) vector test =
      -diskIntegral (diskBulk field) vector (firstTestDerivative direction test) := by
  have ordered : diskIntegral (diskGradient direction field) vector test =
      -diskIntegral (diskBulk field) vector
        (Grad.WeakTesting.orderedTestDerivative 1 (fun _ => direction) test) := by
    fin_cases direction
    · exact (apDiskPairing_literal vector test smooth compact (diskGradX field)).symm.trans
        ((diskGradX_weak field vector test smooth compact supported).trans
          (congrArg Neg.neg (apDiskDerivativePairing_literal vector test smooth compact 1 (fun _ => 0) (diskBulk field))))
    · exact (apDiskPairing_literal vector test smooth compact (diskGradY field)).symm.trans
        ((diskGradY_weak field vector test smooth compact supported).trans
          (congrArg Neg.neg (apDiskDerivativePairing_literal vector test smooth compact 1 (fun _ => 1) (diskBulk field))))
  exact ordered.trans (congrArg (fun value : Spatial → ℝ => -diskIntegral (diskBulk field) vector value)
    (firstTestDerivative_ordered direction test).symm)

theorem diskIntegral_as_pairing (field : DiskL2 1) (vector : PhysicalValue 1)
    (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    diskIntegral field vector test = apDiskPairing 1 0 vector test smooth compact field :=
  (apDiskPairing_literal vector test smooth compact field).symm

theorem diskIntegral_test_add (field : DiskL2 1) (vector : PhysicalValue 1)
    (first second : Spatial → ℝ) (firstSmooth : ContDiff ℝ ∞ first)
    (secondSmooth : ContDiff ℝ ∞ second) (firstCompact : HasCompactSupport first)
    (secondCompact : HasCompactSupport second) :
    diskIntegral field vector (first + second) =
      diskIntegral field vector first + diskIntegral field vector second := by
  simp only [diskIntegral, Pi.add_apply, add_smul]
  exact integral_add (diskIntegral_integrable field vector first firstSmooth firstCompact)
    (diskIntegral_integrable field vector second secondSmooth secondCompact)

theorem firstTestDerivative_supported (direction : Fin 2) (test : Spatial → ℝ) :
    tsupport (firstTestDerivative direction test) ⊆ tsupport test :=
  Grad.WeakTesting.orderedTestDerivative_support_subset _ _ test

end Grad.InteriorLocalization
