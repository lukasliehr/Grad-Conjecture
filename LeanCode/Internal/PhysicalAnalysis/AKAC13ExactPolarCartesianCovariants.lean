import AKAC12ActualScalarCorrectionCurves
import ACP11ExactPolarForceAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.AnnularPhysicalFourier Grad.AnnularKernelL2 Grad.SourceCollarFullSource Grad.SourceCollarAngular
open Grad.AnnularCurrentLow Grad.AnnularCurrentEnergy Grad.Constraints.Gauges Grad.SourceCollar
open Grad.ActualCurrentPrimitives

/-- AD5 polar covariants are converted into AM11 Cartesian covariants by
Q(theta), before the Cartesian inverse transpose is applied. -/
def cartesianCovariantValue (angle : ℝ) (polar : ComplexEuclidean 3) : ComplexEuclidean 3 :=
  WithLp.toLp 2 ((polarDomainMatrix angle).mulVec polar)

theorem cartesianCovariantValue_apply (angle : ℝ) (polar : ComplexEuclidean 3) :
    cartesianCovariantValue angle polar = WithLp.toLp 2
      ![(Real.cos angle : ℂ) * polar 0 - (Real.sin angle : ℂ) * polar 1,
        (Real.sin angle : ℂ) * polar 0 + (Real.cos angle : ℂ) * polar 1,polar 2] := by
  apply PiLp.ext
  intro component
  fin_cases component <;>
    simp [cartesianCovariantValue,polarDomainMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_three,
      physicalRadialVector,physicalTangentialVector,physicalToroidalVector]
  all_goals ring

/-- The AM12 tangential Cartesian correction is precisely the second polar
covariant: (Jy/r) dot w_C = a_c,2. -/
theorem cartesianCovariantValue_tangential (angle : ℝ) (polar : ComplexEuclidean 3) :
    -(Real.sin angle : ℂ) * cartesianCovariantValue angle polar 0 +
      (Real.cos angle : ℂ) * cartesianCovariantValue angle polar 1 = polar 1 := by
  rw [cartesianCovariantValue_apply]
  change -(Real.sin angle : ℂ) * ((Real.cos angle : ℂ) * polar 0 - (Real.sin angle : ℂ) * polar 1) +
    (Real.cos angle : ℂ) * ((Real.sin angle : ℂ) * polar 0 + (Real.cos angle : ℂ) * polar 1) = polar 1
  have circle : (Real.sin angle : ℂ)^2 + (Real.cos angle : ℂ)^2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq angle
  linear_combination polar 1 * circle

/-- Correct original scalar row from the actual annular polar covariants,
using AD8, which is exactly AM12 after the Q rotation above. -/
def polarScalarOverRadiusRow (lower : ℝ) (xiOverRadius : DivisionRow 1 lower)
    (polar : DivisionRow 3 lower) : DivisionRow 1 lower :=
  xiOverRadius + meanFreeRow lower (bulkMatrixUnit lower (0 : Fin 1) (1 : Fin 3) polar)

theorem polarScalarOverRadiusRow_bound (lower : ℝ) (xiOverRadius : DivisionRow 1 lower)
    (polar : DivisionRow 3 lower) :
    ‖polarScalarOverRadiusRow lower xiOverRadius polar‖ ≤ ‖xiOverRadius‖ + ‖polar‖ := by
  have projection := meanFreeRow_bound lower (bulkMatrixUnit lower (0 : Fin 1) (1 : Fin 3) polar)
  have component := bulkMatrixUnit_bound lower (0 : Fin 1) (1 : Fin 3) polar
  have addition := norm_add_le xiOverRadius (meanFreeRow lower (bulkMatrixUnit lower (0 : Fin 1) (1 : Fin 3) polar))
  change ‖xiOverRadius + _‖ ≤ _
  linarith only [projection,component,addition]

def SmoothLowPhysicalRow.polarScalarOverRadius {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {xiOverRadius : DivisionRow 1 lower} {polar : DivisionRow 3 lower}
    (xi : SmoothLowPhysicalRow parameters lower positive xiOverRadius)
    (curves : SmoothLowPhysicalRow parameters lower positive polar) :
    SmoothLowPhysicalRow parameters lower positive (polarScalarOverRadiusRow lower xiOverRadius polar) :=
  xi.add (curves.bulkUnit (0 : Fin 1) 1).meanFree

end Grad.ActualSmoothPhysicalField
