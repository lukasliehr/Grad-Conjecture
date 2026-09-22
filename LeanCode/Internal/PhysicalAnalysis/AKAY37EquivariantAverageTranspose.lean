import AKAY36RoughAngularTransposeDimensions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.RepresentedKernel Grad.RepresentedKernel.WeakDerivatives

def startupAverageWeight (source target : Fin 2) (angle : ℝ) : ℝ :=
  startupInverseRotationEntry source target (-angle)

theorem startupAverageWeight_smooth (source target : Fin 2) : ContDiff ℝ ∞ (startupAverageWeight source target) :=
  (startupInverseRotationEntry_smooth source target).comp contDiff_id.neg

def startupAverageComponentKernel (source target : Fin 2) : StartupL2 2 →L[ℂ] StartupL2 2 :=
  startupAngularKernel 2 (fun angle => (startupAverageWeight source target angle : ℂ))
    (Complex.ofRealCLM.contDiff.comp (startupAverageWeight_smooth source target))

theorem startupAverageCoefficient_coordinate (angle : ℝ) (value : PhysicalValue 2) (source : Fin 2) :
    startupAverageCoefficient angle value source = ∑ target : Fin 2,
      startupAngularCoefficient 2 (fun theta => (startupAverageWeight source target theta : ℂ)) angle value target := by
  fin_cases source <;> simp [startupAverageCoefficient, startupAngularCoefficient,
    startupAverageWeight, startupInverseRotationEntry, planeRotation, spatialDirection,
    rotationValueMap_apply, Fin.sum_univ_two] <;> ring

theorem startupAverageKernel_coordinate_ae (field : StartupL2 2) (cell : ℤ) (source : Fin 2) :
    ∀ᵐ point ∂volume.restrict openUnitDisk,
      (originalAverageKernel field) point cell source =
        ∑ target : Fin 2, (startupAverageComponentKernel source target field) point cell target := by
  have actualIntegrable : ∀ᵐ point ∂volume.restrict openUnitDisk, Integrable
      (fun angle => startupAverageCoefficient angle (field (planeRotationEquiv angle point) cell))
      (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) := by
    simpa only [startupAverageRawData, startupFixedRawData, startupFixedKernelData, if_true] using
      coefficientCell_row_integrable startupAverageRawData cell cell field
  have rows := ae_all_iff.mpr (fun target : Fin 2 => startupAngularKernel_action_ae 2
    (fun angle => (startupAverageWeight source target angle : ℂ))
    (Complex.ofRealCLM.contDiff.comp (startupAverageWeight_smooth source target)) field cell)
  have rowIntegrability := ae_all_iff.mpr (fun target : Fin 2 => startupAngularKernel_row_integrable 2
    (fun angle => (startupAverageWeight source target angle : ℂ))
    (Complex.ofRealCLM.contDiff.comp (startupAverageWeight_smooth source target)) field cell)
  filter_upwards [startupAverageKernel_action_ae field cell, actualIntegrable, rows, rowIntegrability]
    with point actual integrable components componentsIntegrable
  rw [actual]
  have first := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => ℂ) source).integral_comp_comm integrable
  change (∫ angle in Icc (0 : ℝ) (2 * Real.pi), startupAverageCoefficient angle
    (field (planeRotationEquiv angle point) cell)) source = _
  change (∫ angle in Icc (0 : ℝ) (2 * Real.pi), startupAverageCoefficient angle
    (field (planeRotationEquiv angle point) cell) source) =
      (∫ angle in Icc (0 : ℝ) (2 * Real.pi), startupAverageCoefficient angle
        (field (planeRotationEquiv angle point) cell)) source at first
  apply Eq.trans first.symm
  simp_rw [startupAverageCoefficient_coordinate]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro target _
    change _ = (startupAngularKernel 2 (fun angle => (startupAverageWeight source target angle : ℂ))
      (Complex.ofRealCLM.contDiff.comp (startupAverageWeight_smooth source target)) field) point cell target
    rw [components target]
    exact (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => ℂ) target).integral_comp_comm (componentsIntegrable target)
  · intro target _
    exact (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => ℂ) target).integrable_comp (componentsIntegrable target)

theorem startupCoordinatePairing_integrable {dimension : ℕ} (field : StartupL2 dimension) (cell : ℤ)
    (coordinate : Fin dimension) (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    Integrable (fun point => test point • field point cell coordinate) (volume.restrict openUnitDisk) := by
  simpa only [EuclideanSpace.inner_single_left, map_one, one_mul] using
    Grad.WeakTesting.pairing_integrable dimension openUnitDisk cell (EuclideanSpace.single coordinate 1) test
      (smooth.continuous.memLp_of_hasCompactSupport compact) field

/-- Exact real scalar-test transpose of the actual all-cell covariant average. -/
theorem startupAverageKernel_transpose (field : StartupL2 2) (cell : ℤ) (source : Fin 2)
    (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    (∫ point in openUnitDisk, test point • (originalAverageKernel field) point cell source) =
      ∑ target : Fin 2, ∫ point in openUnitDisk,
        startupAngularTest (startupAverageWeight source target) test point • field point cell target := by
  calc
    _ = ∫ point in openUnitDisk, ∑ target : Fin 2,
        test point • (startupAverageComponentKernel source target field) point cell target := by
      apply integral_congr_ae
      filter_upwards [startupAverageKernel_coordinate_ae field cell source] with point actual
      rw [actual, Finset.smul_sum]
    _ = ∑ target : Fin 2, ∫ point in openUnitDisk,
        test point • (startupAverageComponentKernel source target field) point cell target :=
      integral_finsetSum _ (fun target _ => startupCoordinatePairing_integrable
        (startupAverageComponentKernel source target field) cell target test smooth compact)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro target _
      change (∫ point in openUnitDisk, test point •
        (startupAngularKernel 2 (fun angle => (startupAverageWeight source target angle : ℂ))
          (Complex.ofRealCLM.contDiff.comp (startupAverageWeight_smooth source target)) field) point cell target) = _
      simpa only [EuclideanSpace.inner_single_left, map_one, one_mul] using
        startupRealAngularKernel_transposeDim 2 (startupAverageWeight source target)
          (startupAverageWeight_smooth source target) field cell (EuclideanSpace.single target 1) test smooth compact

end Grad.CartesianStartup
