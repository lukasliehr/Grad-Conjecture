import AKAC13ExactPolarCartesianCovariants

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.SourceCollarAngular Grad.AnnularCurrentEnergy

/-- The literal Q(theta) conversion, on the completed original common-weight
row, with unchanged cell frequency and only the two required angular shifts. -/
def cartesianCovariantRow (lower : ℝ) (polar : DivisionRow 3 lower) : DivisionRow 3 lower :=
  bulkMatrixUnit lower (0 : Fin 3) 0 (cosineRow lower 0 polar) -
    bulkMatrixUnit lower (0 : Fin 3) 1 (sineRow lower 0 polar) +
    bulkMatrixUnit lower (1 : Fin 3) 0 (sineRow lower 0 polar) +
    bulkMatrixUnit lower (1 : Fin 3) 1 (cosineRow lower 0 polar) +
    bulkMatrixUnit lower (2 : Fin 3) 2 polar

theorem cosineRow_zero_bound {dimension : ℕ} (lower : ℝ) (row : DivisionRow dimension lower) :
    ‖cosineRow lower 0 row‖ ≤ ‖row‖ := by
  have one := annularRowShiftLinear_norm_le lower 0 1 row
  have two := annularRowShiftLinear_norm_le lower 0 (-1) row
  have total := norm_add_le (annularRowShift lower 0 1 row) (annularRowShift lower 0 (-1) row)
  change ‖annularRowShift lower 0 1 row‖ ≤ _ at one
  change ‖annularRowShift lower 0 (-1) row‖ ≤ _ at two
  unfold cosineRow
  rw [norm_smul]
  norm_num [norm_inv] at *
  linarith only [one,two,total]

theorem sineRow_zero_bound {dimension : ℕ} (lower : ℝ) (row : DivisionRow dimension lower) :
    ‖sineRow lower 0 row‖ ≤ ‖row‖ := by
  have one := annularRowShiftLinear_norm_le lower 0 1 row
  have two := annularRowShiftLinear_norm_le lower 0 (-1) row
  have total := norm_sub_le (annularRowShift lower 0 1 row) (annularRowShift lower 0 (-1) row)
  change ‖annularRowShift lower 0 1 row‖ ≤ _ at one
  change ‖annularRowShift lower 0 (-1) row‖ ≤ _ at two
  unfold sineRow
  rw [norm_smul]
  norm_num [norm_inv,norm_mul] at *
  linarith only [one,two,total]

/-- No inner-radius or analytic-width loss is introduced by the compulsory
polar-to-Cartesian covariant conversion. -/
theorem cartesianCovariantRow_bound (lower : ℝ) (polar : DivisionRow 3 lower) :
    ‖cartesianCovariantRow lower polar‖ ≤ 5 * ‖polar‖ := by
  have cosine := cosineRow_zero_bound lower polar
  have sine := sineRow_zero_bound lower polar
  have a := bulkMatrixUnit_bound lower (0 : Fin 3) (0 : Fin 3) (cosineRow lower 0 polar)
  have b := bulkMatrixUnit_bound lower (0 : Fin 3) (1 : Fin 3) (sineRow lower 0 polar)
  have c := bulkMatrixUnit_bound lower (1 : Fin 3) (0 : Fin 3) (sineRow lower 0 polar)
  have d := bulkMatrixUnit_bound lower (1 : Fin 3) (1 : Fin 3) (cosineRow lower 0 polar)
  have e := bulkMatrixUnit_bound lower (2 : Fin 3) (2 : Fin 3) polar
  have ab := norm_sub_le (bulkMatrixUnit lower (0 : Fin 3) 0 (cosineRow lower 0 polar))
    (bulkMatrixUnit lower (0 : Fin 3) 1 (sineRow lower 0 polar))
  have abc := norm_add_le
    (bulkMatrixUnit lower (0 : Fin 3) 0 (cosineRow lower 0 polar) - bulkMatrixUnit lower (0 : Fin 3) 1 (sineRow lower 0 polar))
    (bulkMatrixUnit lower (1 : Fin 3) 0 (sineRow lower 0 polar))
  have abcd := norm_add_le
    (bulkMatrixUnit lower (0 : Fin 3) 0 (cosineRow lower 0 polar) - bulkMatrixUnit lower (0 : Fin 3) 1 (sineRow lower 0 polar) +
      bulkMatrixUnit lower (1 : Fin 3) 0 (sineRow lower 0 polar))
    (bulkMatrixUnit lower (1 : Fin 3) 1 (cosineRow lower 0 polar))
  have all := norm_add_le
    (bulkMatrixUnit lower (0 : Fin 3) 0 (cosineRow lower 0 polar) - bulkMatrixUnit lower (0 : Fin 3) 1 (sineRow lower 0 polar) +
      bulkMatrixUnit lower (1 : Fin 3) 0 (sineRow lower 0 polar) + bulkMatrixUnit lower (1 : Fin 3) 1 (cosineRow lower 0 polar))
    (bulkMatrixUnit lower (2 : Fin 3) 2 polar)
  change ‖_+_‖ ≤ _
  linarith only [cosine,sine,a,b,c,d,e,ab,abc,abcd,all]

end Grad.ActualSmoothPhysicalField
