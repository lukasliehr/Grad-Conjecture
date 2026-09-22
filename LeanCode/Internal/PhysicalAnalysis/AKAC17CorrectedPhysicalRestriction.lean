import AKAC16CorrectedPhysicalVectorAction
import AKG14GenuineCompactFluxLocality

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.SourceCollarAngular Grad.AnnularCurrentEnergy Grad.AnnularRestriction
open Grad.ActualPhysicalField Grad.GaugeCoefficients.Physical.Allocation

variable (lower upper : ℝ) (included : lower ≤ upper)

theorem originalBulkRestriction_angularShift {dimension : ℕ} (power : ℕ) (shift : ℤ)
    (row : DivisionRow dimension lower) :
    originalBulkRestriction dimension lower upper included (annularRowShift lower power shift row) =
      annularRowShift upper power shift (originalBulkRestriction dimension lower upper included row) := by
  apply lp.ext
  funext mode
  change collarL2Restriction dimension lower upper included (annularShiftScalar power shift mode • row (mode.1-shift,mode.2)) =
    annularShiftScalar power shift mode • collarL2Restriction dimension lower upper included (row (mode.1-shift,mode.2))
  exact map_smul _ _ _

theorem originalBulkRestriction_cosine {dimension : ℕ} (row : DivisionRow dimension lower) :
    originalBulkRestriction dimension lower upper included (cosineRow lower 0 row) =
      cosineRow upper 0 (originalBulkRestriction dimension lower upper included row) := by
  unfold cosineRow
  rw [map_smul,map_add,originalBulkRestriction_angularShift,originalBulkRestriction_angularShift]

theorem originalBulkRestriction_sine {dimension : ℕ} (row : DivisionRow dimension lower) :
    originalBulkRestriction dimension lower upper included (sineRow lower 0 row) =
      sineRow upper 0 (originalBulkRestriction dimension lower upper included row) := by
  unfold sineRow
  rw [map_smul,map_sub,originalBulkRestriction_angularShift,originalBulkRestriction_angularShift]

theorem originalBulkRestriction_meanFree {dimension : ℕ} (row : DivisionRow dimension lower) :
    originalBulkRestriction dimension lower upper included (meanFreeRow lower row) =
      meanFreeRow upper (originalBulkRestriction dimension lower upper included row) := by
  apply lp.ext
  funext mode
  change collarL2Restriction dimension lower upper included (if mode.1=0 then 0 else row mode) =
    if mode.1=0 then 0 else collarL2Restriction dimension lower upper included (row mode)
  split_ifs <;> simp

theorem cartesianCovariantRow_restriction (row : DivisionRow 3 lower) :
    originalBulkRestriction 3 lower upper included (cartesianCovariantRow lower row) =
      cartesianCovariantRow upper (originalBulkRestriction 3 lower upper included row) := by
  unfold cartesianCovariantRow
  simp only [map_add,map_sub,bulkMatrixUnit_restriction,originalBulkRestriction_cosine,originalBulkRestriction_sine]

theorem polarScalarOverRadiusRow_restriction (xi : DivisionRow 1 lower) (polar : DivisionRow 3 lower) :
    originalBulkRestriction 1 lower upper included (polarScalarOverRadiusRow lower xi polar) =
      polarScalarOverRadiusRow upper (originalBulkRestriction 1 lower upper included xi)
        (originalBulkRestriction 3 lower upper included polar) := by
  unfold polarScalarOverRadiusRow
  rw [map_add,originalBulkRestriction_meanFree,bulkMatrixUnit_restriction]

theorem physicalUFromPolar_restriction (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (bounded : upper ≤ 1) (polar : DivisionRow 3 lower) :
    originalBulkRestriction 3 lower upper included
      (physicalUFromPolar parameters length rho epsilon base small lower lowerPositive (included.trans bounded) polar) =
      physicalUFromPolar parameters length rho epsilon base small upper upperPositive bounded
        (originalBulkRestriction 3 lower upper included polar) := by
  unfold physicalUFromPolar
  rw [physicalUFromCovariant_restriction,cartesianCovariantRow_restriction]

end Grad.ActualSmoothPhysicalField
