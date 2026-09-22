import AKAC15AngularRotationSmoothCurves

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.SourceCollarAngular Grad.AnnularCurrentEnergy
open Grad.ActualPhysicalField Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)

/-- The actual Cartesian inverse transpose is applied to Q(theta) a_c.
Applying it directly to the polar a_c would use the wrong frame. -/
def physicalUFromPolar (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (polar : DivisionRow 3 lower) : DivisionRow 3 lower :=
  physicalUFromCovariant parameters length rho epsilon base small 0 lower positive bounded
    (cartesianCovariantRow lower polar)

theorem physicalUFromPolar_bound (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (polar : DivisionRow 3 lower) :
    ‖physicalUFromPolar parameters length rho epsilon base small lower positive bounded polar‖ ≤
      5 * physicalUActionConstant parameters length 0 *
        (1 + physicalBudget parameters base rho epsilon 5) * ‖polar‖ := by
  have estimate := originalInverseTransposeFamily_estimate parameters length rho epsilon base small
  have constant : 0 ≤ physicalUActionConstant parameters length 0 :=
    mul_nonneg (physicalMatrixKernelConstant_nonnegative parameters 3 3 0)
      (add_nonneg (estimate.fixedNonnegative 1) (estimate.deviationNonnegative 1))
  have multiplier : 0 ≤ physicalUActionConstant parameters length 0 *
      (1+physicalBudget parameters base rho epsilon 5) :=
    mul_nonneg constant (by linarith [physicalBudget_nonnegative parameters base rho epsilon 5])
  have actual := physicalUFromCovariant_bound parameters length rho epsilon base small 0 lower positive bounded
    (cartesianCovariantRow lower polar)
  have rotation := mul_le_mul_of_nonneg_left (cartesianCovariantRow_bound lower polar) multiplier
  exact actual.trans (rotation.trans_eq (by ring))

/-- All original phase-weighted radial grades for the corrected SAME U. -/
def SmoothLowPhysicalRow.physicalUFromPolar (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row) :
    SmoothLowPhysicalRow parameters lower positive
      (physicalUFromPolar parameters length rho epsilon base small lower positive bounded.le row) :=
  curves.cartesianCovariant.physicalU parameters length rho epsilon base small lower positive bounded

end Grad.ActualSmoothPhysicalField
