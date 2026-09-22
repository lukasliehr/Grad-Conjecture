import AKAY38GenuineRadialProjectionTranspose

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger

theorem startupIntegrable_real_smul (function : Spatial → ℂ)
    (integrable : Integrable function (volume.restrict openUnitDisk)) (scalar : ℝ) :
    Integrable (fun point => scalar • function point) (volume.restrict openUnitDisk) :=
  (scalar • ContinuousLinearMap.id ℝ ℂ).integrable_comp integrable

theorem startupIntegral_affine_three (first second third : Spatial → ℂ)
    (firstIntegrable : Integrable first (volume.restrict openUnitDisk))
    (secondIntegrable : Integrable second (volume.restrict openUnitDisk))
    (thirdIntegrable : Integrable third (volume.restrict openUnitDisk)) (delta half sign : ℝ) :
    (∫ point in openUnitDisk, delta • first point - half • (second point + sign • third point)) =
      delta • (∫ point in openUnitDisk, first point) - half •
        ((∫ point in openUnitDisk, second point) + sign • (∫ point in openUnitDisk, third point)) := by
  have last := startupIntegrable_real_smul third thirdIntegrable sign
  have middle : Integrable (fun point => second point + sign • third point) (volume.restrict openUnitDisk) :=
    secondIntegrable.add last
  rw [integral_sub (startupIntegrable_real_smul first firstIntegrable delta)
    (startupIntegrable_real_smul _ middle half), integral_smul, integral_smul,
    integral_add secondIntegrable last, integral_smul]

theorem startupRawQradTest_pairing_component (field : StartupL2 2) (cell : ℤ) (source target : Fin 2)
    (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    (∫ point in openUnitDisk, startupRawQradTest source test target point • field point cell target) =
      (if target = source then 1 else 0 : ℝ) • (∫ point in openUnitDisk, test point • field point cell target) -
        (1 / 2 : ℝ) •
          ((∫ point in openUnitDisk, startupAngularTest (startupAverageWeight source target) test point • field point cell target) +
            (if source = 0 then 1 else -1 : ℝ) •
              (∫ point in openUnitDisk, startupAngularTest (startupAverageWeight source target)
                (fun query => test (cartesianReflectionEquiv query)) point • field point cell target)) := by
  have first := startupCoordinatePairing_integrable field cell target test smooth compact
  have average := startupCoordinatePairing_integrable field cell target
    (startupAngularTest (startupAverageWeight source target) test)
    (startupAngularTest_smooth _ (startupAverageWeight_smooth source target) test smooth)
    (startupAngularTest_compact _ test compact)
  have reflected := startupCoordinatePairing_integrable field cell target
    (startupAngularTest (startupAverageWeight source target) (fun query => test (cartesianReflectionEquiv query)))
    (startupAngularTest_smooth _ (startupAverageWeight_smooth source target) _
      (smooth.comp cartesianReflectionEquiv.toContinuousLinearEquiv.toContinuousLinearMap.contDiff))
    (startupAngularTest_compact _ _ (compact.comp_homeomorph cartesianReflectionEquiv.toHomeomorph))
  change (∫ point in openUnitDisk,
    ((if target = source then 1 else 0 : ℝ) * test point - (1 / 2 : ℝ) *
      (startupAngularTest (startupAverageWeight source target) test point +
        (if source = 0 then 1 else -1 : ℝ) * startupAngularTest (startupAverageWeight source target)
          (fun query => test (cartesianReflectionEquiv query)) point)) • field point cell target) = _
  simp only [sub_smul, mul_smul, add_smul]
  exact startupIntegral_affine_three
    (fun point => test point • field point cell target)
    (fun point => startupAngularTest (startupAverageWeight source target) test point • field point cell target)
    (fun point => startupAngularTest (startupAverageWeight source target)
      (fun query => test (cartesianReflectionEquiv query)) point • field point cell target)
    first average reflected (if target = source then 1 else 0 : ℝ) (1 / 2 : ℝ)
    (if source = 0 then 1 else -1 : ℝ)


/-- Exact compact-test transpose of the genuine I+JTJ projector. This is the
literal unbundled test operator supplied to original axis removal. -/
theorem startupGenuineQrad_rawTranspose (field : StartupL2 2) (cell : ℤ) (source : Fin 2)
    (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    (∫ point in openUnitDisk, test point • (startupGenuineQradKernel field) point cell source) =
      ∑ target : Fin 2, ∫ point in openUnitDisk,
        startupRawQradTest source test target point • field point cell target := by
  rw [startupGenuineQrad_transpose_expanded field cell source test smooth compact]
  simp_rw [startupRawQradTest_pairing_component field cell source _ test smooth compact]
  fin_cases source <;> simp only [Fin.sum_univ_two] <;> norm_num <;> module

end Grad.CartesianStartup
