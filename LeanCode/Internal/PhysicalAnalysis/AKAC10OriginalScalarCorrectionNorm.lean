import AKAC9PeriodicSameVectorField
import SCS14PolarCoefficientFormula

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.AnnularPhysicalFourier Grad.AnnularKernelL2 Grad.SourceCollarFullSource Grad.SourceCollarAngular
open Grad.AnnularCurrentLow Grad.AnnularCurrentEnergy

/-- The two planar covariant components, in the unchanged original common
radial weight. -/
def planarCovariantRow (lower : ℝ) (covariant : DivisionRow 3 lower) : DivisionRow 2 lower :=
  bulkMatrixUnit lower (0 : Fin 2) (0 : Fin 3) covariant +
    bulkMatrixUnit lower (1 : Fin 2) (1 : Fin 3) covariant

theorem planarCovariantRow_bound (lower : ℝ) (covariant : DivisionRow 3 lower) :
    ‖planarCovariantRow lower covariant‖ ≤ 2 * ‖covariant‖ := by
  exact (norm_add_le _ _).trans ((add_le_add
    (bulkMatrixUnit_bound lower (0 : Fin 2) (0 : Fin 3) covariant)
    (bulkMatrixUnit_bound lower (1 : Fin 2) (1 : Fin 3) covariant)).trans_eq (by ring))

/-- AM12 divided by radius: S/r = Xi/r + P((Jy/r) dot u).
The second term is the original tangential contraction, with angular mean
removed and no cell frequency projection or new radial factor. -/
def originalScalarOverRadiusRow (lower : ℝ) (positive : 0 < lower)
    (xiOverRadius : DivisionRow 1 lower) (covariant : DivisionRow 3 lower) : DivisionRow 1 lower :=
  xiOverRadius + meanFreeRow lower
    (tangentialRowContraction lower positive 0 (planarCovariantRow lower covariant))

/-- A radius-independent common-weight bound for the original S/r.
The covariant correction cannot be omitted from the scalar energy. -/
theorem originalScalarOverRadiusRow_bound (lower : ℝ) (positive : 0 < lower)
    (xiOverRadius : DivisionRow 1 lower) (covariant : DivisionRow 3 lower) :
    ‖originalScalarOverRadiusRow lower positive xiOverRadius covariant‖ ≤
      ‖xiOverRadius‖ + 4 * ‖covariant‖ := by
  have tangential := tangentialRowContraction_bound lower positive 0 (planarCovariantRow lower covariant)
  have mean := meanFreeRow_bound lower (tangentialRowContraction lower positive 0 (planarCovariantRow lower covariant))
  have planar := planarCovariantRow_bound lower covariant
  have total := norm_add_le xiOverRadius
    (meanFreeRow lower (tangentialRowContraction lower positive 0 (planarCovariantRow lower covariant)))
  change ‖xiOverRadius + _‖ ≤ _
  norm_num only [pow_zero,mul_one] at tangential
  linarith only [tangential,mean,planar,total]

theorem originalScalarOverRadiusRow_sq_bound (lower : ℝ) (positive : 0 < lower)
    (xiOverRadius : DivisionRow 1 lower) (covariant : DivisionRow 3 lower) :
    ‖originalScalarOverRadiusRow lower positive xiOverRadius covariant‖ ^ 2 ≤
      2 * ‖xiOverRadius‖ ^ 2 + 32 * ‖covariant‖ ^ 2 := by
  have bound := originalScalarOverRadiusRow_bound lower positive xiOverRadius covariant
  have square := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr bound
  nlinarith [sq_nonneg (‖xiOverRadius‖ - 4 * ‖covariant‖)]

end Grad.ActualSmoothPhysicalField
