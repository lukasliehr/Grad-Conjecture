import AKAX4ExactTestCovectors

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

open Set MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.RepresentedKernel.SpatialProduct Grad.GenericCarriers

/-- The actual real inverse-covector weight. -/
def startupRealCovectorWeight (weight : ℝ → ℝ) (direction coordinate : Fin 2) (angle : ℝ) : ℝ :=
  weight angle * startupInverseRotationEntry direction coordinate angle

theorem startupRealCovectorWeight_smooth (weight : ℝ → ℝ) (smooth : ContDiff ℝ ∞ weight)
    (direction coordinate : Fin 2) : ContDiff ℝ ∞ (startupRealCovectorWeight weight direction coordinate) :=
  smooth.mul (startupInverseRotationEntry_smooth direction coordinate)

theorem startupTestDerivative_smooth (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test)
    (direction : Fin 2) : ContDiff ℝ ∞ (directionDerivative direction test) :=
  contDiffOn_univ.mp (directionDerivative_smooth isOpen_univ direction smooth.contDiffOn)

theorem startupTestDerivative_compact (test : Spatial → ℝ) (compact : HasCompactSupport test)
    (direction : Fin 2) : HasCompactSupport (directionDerivative direction test) :=
  (compact.fderiv (𝕜 := ℝ)).comp_left (g := fun derivative : Spatial →L[ℝ] ℝ =>
    derivative (spatialDirection direction)) rfl

theorem startupAngularTest_derivative (weight : ℝ → ℝ) (weightSmooth : ContDiff ℝ ∞ weight)
    (test : Spatial → ℝ) (testSmooth : ContDiff ℝ ∞ test) (direction : Fin 2) (point : Spatial) :
    directionDerivative direction (startupAngularTest weight test) point =
      ∑ coordinate : Fin 2, startupAngularTest (startupRealCovectorWeight weight direction coordinate)
        (directionDerivative coordinate test) point := by
  change fderiv ℝ (startupAngularTest weight test) point (spatialDirection direction) = _
  rw [startupAngularTest_derivative_integral weight weightSmooth test testSmooth]
  have rotationContinuous : Continuous (fun angle : ℝ => planeRotationEquiv (-angle) point) := by
    have insertion : ContDiff ℝ ∞ (fun angle : ℝ => (point, angle)) :=
      contDiff_const.prodMk contDiff_id
    simpa only [Function.comp_def] using (startupInverseTestRotation_smooth.comp insertion).continuous
  have rows (coordinate : Fin 2) : IntegrableOn (fun angle : ℝ =>
      (weight angle * startupInverseRotationEntry direction coordinate angle) *
        fderiv ℝ test (planeRotationEquiv (-angle) point) (spatialDirection coordinate))
      (Icc (0 : ℝ) (2 * Real.pi)) :=
    (((weightSmooth.continuous).mul (startupInverseRotationEntry_smooth direction coordinate).continuous).mul
      (((testSmooth.continuous_fderiv (by simp)).comp rotationContinuous).clm_apply continuous_const)).integrableOn_Icc
  rw [integral_finsetSum _ (fun coordinate _ => rows coordinate), Finset.mul_sum]
  rfl

/-- The genuine weak first-derivative transfer for the actual full-cell angular action.
 This assumes no H1 regularity of the field and no derivative commutation. -/
theorem startupAngular_derivative_transpose (weight : ℝ → ℝ) (weightSmooth : ContDiff ℝ ∞ weight)
    (test : Spatial → ℝ) (testSmooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    (field : StartupL2 3) (cell : ℤ) (vector : PhysicalValue 3) (direction : Fin 2) :
    (∫ point in openUnitDisk, directionDerivative direction (startupAngularTest weight test) point •
      inner ℂ vector (field point cell)) =
      ∑ coordinate : Fin 2, ∫ point in openUnitDisk, directionDerivative coordinate test point •
        inner ℂ vector ((startupRealAngularKernel (startupRealCovectorWeight weight direction coordinate)
          (startupRealCovectorWeight_smooth weight weightSmooth direction coordinate) field) point cell) := by
  have rows (coordinate : Fin 2) : Integrable (fun point : Spatial =>
      startupAngularTest (startupRealCovectorWeight weight direction coordinate)
        (directionDerivative coordinate test) point • inner ℂ vector (field point cell))
      (volume.restrict openUnitDisk) :=
    Grad.WeakTesting.pairing_integrable 3 openUnitDisk cell vector _
      ((startupAngularTest_smooth _ (startupRealCovectorWeight_smooth weight weightSmooth direction coordinate) _
        (startupTestDerivative_smooth test testSmooth coordinate)).continuous.memLp_of_hasCompactSupport
          (startupAngularTest_compact _ _ (startupTestDerivative_compact test compact coordinate))) field
  simp_rw [startupAngularTest_derivative weight weightSmooth test testSmooth direction, Finset.sum_smul]
  rw [integral_finsetSum _ (fun coordinate _ => rows coordinate)]
  apply Finset.sum_congr rfl
  intro coordinate _
  exact (startupRealAngularKernel_transpose _
    (startupRealCovectorWeight_smooth weight weightSmooth direction coordinate) field cell vector
    (directionDerivative coordinate test) (startupTestDerivative_smooth test testSmooth coordinate)
    (startupTestDerivative_compact test compact coordinate)).symm

end Grad.CartesianStartup
