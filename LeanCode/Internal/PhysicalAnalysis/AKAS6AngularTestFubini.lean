import AKAS3TrueInverseTensorKernels
import RKWD1Fubini

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

open MeasureTheory Set
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.RepresentedKernel Grad.RepresentedKernel.WeakDerivatives

/-- Reuse the actual fixed weak-kernel construction for the same angular coefficient. -/
def startupAngularRawData (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight) :
    RawKernelData (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) 3 3 openUnitDisk :=
  startupFixedRawData (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) planeRotationEquiv
    (fun angle => by
      intro point
      change (‖planeRotationEquiv angle point‖ < 1 ↔ ‖point‖ < 1)
      rw [(planeRotationEquiv angle).norm_map])
    continuous_planeRotation_joint.measurable (startupAngularCoefficient 3 weight)
    (startupAngularCoefficient_continuous 3 weight smooth).measurable
    (startupAngularCoefficient_continuous 3 weight smooth).integrableOn_Icc

/-- Actual all-cell angular action tested against an L2 scalar test.
 The change in integration order is inherited from the proved weak-kernel
 Fubini theorem, with no finite-cell truncation hypothesis. -/
theorem startupAngularKernel_testFubini (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight)
    (field : StartupL2 3) (cell : ℤ) (vector : PhysicalValue 3)
    (test : Spatial → ℝ) (testMeasurable : Measurable test)
    (testLp : MemLp test 2 (volume.restrict openUnitDisk)) :
    (∫ point in openUnitDisk, test point • inner ℂ vector
      (fieldCellProjection 3 openUnitDisk cell (startupAngularKernel 3 weight smooth field) point)) =
      ∫ angle in Icc (0 : ℝ) (2 * Real.pi), ∫ point in openUnitDisk,
        test point • inner ℂ vector
          (startupAngularCoefficient 3 weight angle (field (planeRotationEquiv angle point) cell)) := by
  have fubini := coefficientCell_pairing_fubini (startupAngularRawData weight smooth)
    cell cell field test testMeasurable testLp vector
  simp only [startupAngularRawData, startupFixedRawData, startupFixedKernelData, if_true] at fubini
  change (∫ point in openUnitDisk, test point • inner ℂ vector
    (∫ angle in Icc (0 : ℝ) (2 * Real.pi),
      startupAngularCoefficient 3 weight angle (field (planeRotationEquiv angle point) cell))) = _ at fubini
  apply Eq.trans _ fubini
  apply integral_congr_ae
  filter_upwards [Grad.FullCellKernel.entry_field_ae (startupAngularKernelData 3 weight smooth)
    field cell cell] with point represented
  rw [startupAngularKernel_coordinate]
  simp only [startupAngularKernelData, startupFixedKernelData, if_true] at represented
  change _ = ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
    startupAngularCoefficient 3 weight angle (field (planeRotationEquiv angle point) cell) at represented
  exact congrArg (fun value : PhysicalValue 3 => test point • inner ℂ vector value) represented

end Grad.CartesianStartup
