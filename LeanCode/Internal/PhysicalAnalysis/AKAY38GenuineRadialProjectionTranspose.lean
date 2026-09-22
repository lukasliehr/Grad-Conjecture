import AKAY37EquivariantAverageTranspose

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger

theorem startupReflectionValue_coordinate (source : Fin 2) (value : PhysicalValue 2) :
    reflectionValueMap value source = (if source = 0 then 1 else -1 : ℝ) • value source := by
  fin_cases source <;> simp [reflectionValueMap, reflectionValueLinear]

theorem startupReflectionKernel_transpose (field : StartupL2 2) (cell : ℤ) (source : Fin 2) (test : Spatial → ℝ) :
    (∫ point in openUnitDisk, test point •
      (startupPointKernel reflectionValueMap cartesianReflectionEquiv field) point cell source) =
      (if source = 0 then 1 else -1 : ℝ) •
        ∫ point in openUnitDisk, test (cartesianReflectionEquiv point) • field point cell source := by
  have changed := (startupOrthogonal_disk_preserving cartesianReflectionEquiv).integral_comp
    cartesianReflectionEquiv.toHomeomorph.measurableEmbedding
    (fun point : Spatial => test (cartesianReflectionEquiv.symm point) • reflectionValueMap (field point cell) source)
  calc
    _ = ∫ point in openUnitDisk, test point • reflectionValueMap (field (cartesianReflectionEquiv point) cell) source := by
      apply integral_congr_ae
      filter_upwards [startupPointKernel_field_ae reflectionValueMap cartesianReflectionEquiv field] with point actual
      rw [actual cell]
    _ = ∫ point in openUnitDisk, test (cartesianReflectionEquiv point) • reflectionValueMap (field point cell) source := by
      have inverse : cartesianReflectionEquiv.symm = cartesianReflectionEquiv := by
        apply LinearIsometryEquiv.ext
        intro point
        apply cartesianReflectionEquiv.injective
        rw [LinearIsometryEquiv.apply_symm_apply]
        change point = cartesianReflection (cartesianReflection point)
        apply PiLp.ext
        intro coordinate
        fin_cases coordinate <;> simp [cartesianReflection]
      simp only [LinearIsometryEquiv.symm_apply_apply] at changed
      rw [inverse] at changed
      exact changed
    _ = _ := by
      simp_rw [startupReflectionValue_coordinate, smul_comm (test _) (if source = 0 then 1 else -1 : ℝ)]
      exact integral_smul _ _

theorem startupGenuineQrad_transpose_expanded (field : StartupL2 2) (cell : ℤ) (source : Fin 2)
    (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    (∫ point in openUnitDisk, test point • (startupGenuineQradKernel field) point cell source) =
      (∫ point in openUnitDisk, test point • field point cell source) - (1 / 2 : ℝ) •
        ((∑ target : Fin 2, ∫ point in openUnitDisk,
          startupAngularTest (startupAverageWeight source target) test point • field point cell target) +
          (if source = 0 then 1 else -1 : ℝ) •
          (∑ target : Fin 2, ∫ point in openUnitDisk,
            startupAngularTest (startupAverageWeight source target)
              (fun query => test (cartesianReflectionEquiv query)) point • field point cell target)) := by
  let functional := Grad.WeakTesting.compactPairing 2 openUnitDisk cell
    (EuclideanSpace.single source 1) test smooth compact
  have actual (value : StartupL2 2) : functional value =
      ∫ point in openUnitDisk, test point • value point cell source := by
    simpa only [EuclideanSpace.inner_single_left, map_one, one_mul] using
      Grad.WeakTesting.compactPairing_apply 2 openUnitDisk cell (EuclideanSpace.single source 1) test smooth compact value
  rw [← actual, startupGenuineQrad_reflection, map_sub, map_smul, map_add,
    actual field, actual (originalAverageKernel field),
    actual (startupPointKernel reflectionValueMap cartesianReflectionEquiv (originalAverageKernel field))]
  rw [startupReflectionKernel_transpose, startupAverageKernel_transpose field cell source test smooth compact,
    startupAverageKernel_transpose field cell source (fun query => test (cartesianReflectionEquiv query))
      (smooth.comp cartesianReflectionEquiv.toContinuousLinearEquiv.toContinuousLinearMap.contDiff)
      (compact.comp_homeomorph cartesianReflectionEquiv.toHomeomorph)]
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.coe_smul]

end Grad.CartesianStartup
