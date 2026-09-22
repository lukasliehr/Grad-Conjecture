import AKBP12LocalizedEquationSupport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set MeasureTheory
open scoped ContDiff Topology
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets Grad.WeightedJets.ZeroExtension
open Grad.RepresentedKernel.SpatialProduct

def startupSmoothPairing (field : StartupL2 3) (cell : ℤ) (vector : PhysicalValue 3) (test : Spatial → ℝ) : ℂ :=
  ∫ point in openUnitDisk, test point • inner ℂ vector (field point cell)

theorem startupLocalizeSmoothTest_first_germ {support : Set Spatial}
    (localizer : TestLocalizer openUnitDisk support) (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test)
    (point : Spatial) (inside : point ∈ support) (direction : Fin 2) :
    directionDerivative direction (startupLocalizeSmoothTest localizer test smooth).toFun =ᶠ[𝓝 point]
      directionDerivative direction test := by
  have germ : fderiv ℝ (startupLocalizeSmoothTest localizer test smooth).toFun =ᶠ[𝓝 point] fderiv ℝ test :=
    (startupLocalizeSmoothTest_germ localizer test smooth point inside).fderiv
  filter_upwards [germ] with source same
  exact congrArg (fun derivative : Spatial →L[ℝ] ℝ => derivative (spatialDirection direction)) same

theorem startupSupportedPairing_localize {support : Set Spatial}
    (localizer : TestLocalizer openUnitDisk support) (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test)
    (field : StartupL2 3) (supported : SupportedField (CellValues 3) openUnitDisk support field)
    (cell : ℤ) (vector : PhysicalValue 3) :
    startupTestPairing cell vector (startupLocalizeSmoothTest localizer test smooth) field =
      startupSmoothPairing field cell vector test := by
  rw [startupTestPairing_apply]
  exact integral_supported_congr 3 openUnitDisk support field supported cell vector _ _
    (fun point inside => (startupLocalizeSmoothTest_germ localizer test smooth point inside).eq_of_nhds)

theorem startupSupportedPairing_localize_first {support : Set Spatial}
    (localizer : TestLocalizer openUnitDisk support) (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test)
    (field : StartupL2 3) (supported : SupportedField (CellValues 3) openUnitDisk support field)
    (cell : ℤ) (vector : PhysicalValue 3) (direction : Fin 2) :
    startupTestPairing cell vector (startupDerivativeTest direction (startupLocalizeSmoothTest localizer test smooth)) field =
      startupSmoothPairing field cell vector (directionDerivative direction test) := by
  rw [startupTestPairing_apply]
  exact integral_supported_congr 3 openUnitDisk support field supported cell vector _ _
    (fun point inside => (startupLocalizeSmoothTest_first_germ localizer test smooth point inside direction).eq_of_nhds)

theorem startupSupportedPairing_localize_second {support : Set Spatial}
    (localizer : TestLocalizer openUnitDisk support) (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test)
    (field : StartupL2 3) (supported : SupportedField (CellValues 3) openUnitDisk support field)
    (cell : ℤ) (vector : PhysicalValue 3) (outer inner : Fin 2) :
    startupTestPairing cell vector (startupDerivativeTest outer
      (startupDerivativeTest inner (startupLocalizeSmoothTest localizer test smooth))) field =
      startupSmoothPairing field cell vector (directionDerivative outer (directionDerivative inner test)) := by
  rw [startupTestPairing_apply]
  apply integral_supported_congr 3 openUnitDisk support field supported cell vector
  intro point inside
  exact congrArg (fun derivative : Spatial →L[ℝ] ℝ => derivative (spatialDirection outer))
    (startupLocalizeSmoothTest_first_germ localizer test smooth point inside inner).fderiv_eq

/-- All smooth tests are legitimate for the SAME compactly supported equation,
using the retained localizer's equality of germs to preserve two derivatives. -/
theorem startupCompactEquation_smoothTests {support : Set Spatial}
    (localizer : TestLocalizer openUnitDisk support) (field zeroth : StartupL2 3)
    (tensor : Fin 2 → Fin 2 → StartupL2 3) (flux : Fin 2 → StartupL2 3)
    (fieldSupported : SupportedField (CellValues 3) openUnitDisk support field)
    (zeroSupported : SupportedField (CellValues 3) openUnitDisk support zeroth)
    (tensorSupported : ∀ outer inner, SupportedField (CellValues 3) openUnitDisk support (tensor outer inner))
    (fluxSupported : ∀ direction, SupportedField (CellValues 3) openUnitDisk support (flux direction))
    (equation : StartupWeakDivDivEquation field zeroth tensor flux)
    (cell : ℤ) (vector : PhysicalValue 3) (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) :
    (∑ direction : Fin 2, startupSmoothPairing field cell vector (directionDerivative direction (directionDerivative direction test))) =
      (∑ outer : Fin 2, ∑ inner : Fin 2, startupSmoothPairing (tensor outer inner) cell vector
        (directionDerivative outer (directionDerivative inner test))) +
      startupSmoothPairing zeroth cell vector test +
      ∑ direction : Fin 2, startupSmoothPairing (flux direction) cell vector (directionDerivative direction test) := by
  have identity := equation cell vector (startupLocalizeSmoothTest localizer test smooth)
  rw [startupLaplacianTest,startupTestPairing_add,add_apply] at identity
  rw [startupSupportedPairing_localize_second localizer test smooth field fieldSupported cell vector 0 0,
    startupSupportedPairing_localize_second localizer test smooth field fieldSupported cell vector 1 1,
    startupSupportedPairing_localize localizer test smooth zeroth zeroSupported cell vector] at identity
  simp_rw [startupSupportedPairing_localize_second localizer test smooth _ (tensorSupported _ _) cell vector,
    startupSupportedPairing_localize_first localizer test smooth _ (fluxSupported _) cell vector] at identity
  simpa only [Fin.sum_univ_two] using identity

end Grad.CartesianStartup
