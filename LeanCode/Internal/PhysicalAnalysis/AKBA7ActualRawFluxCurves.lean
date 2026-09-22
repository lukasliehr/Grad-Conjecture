import AKBA6LiteralPolarRowsAndColumns
import AKBA4SameOriginalVectorRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
open scoped ContDiff
namespace Grad.OriginalKernelGraphRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra Grad.AnnularCurrentEnergy
open Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction Grad.ActualSmoothPhysicalField
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.OriginalKernelRetainedDecay Grad.SourceCollarAngular

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 8 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    {vectorRow : DivisionRow 3 lower} {xiRow : DivisionRow 1 lower}
    (vector : SmoothLowPhysicalRow parameters lower positive vectorRow)
    (xi : SmoothLowPhysicalRow parameters lower positive xiRow)

/-- Actual fixed-collar full weighted curves of C U+kappa xi/r. The row is
constructed by the existing completed matrix and trigonometric actions. -/
def originalRawFluxCurves : (row : DivisionRow 1 lower) × SmoothLowPhysicalRow parameters lower positive row :=
  let low := (originalAxis_primitive_margin parameters length rho epsilon base small).1
  let covector := vector.matrixAction parameters (originalCofactorCovectorFamily parameters length epsilon base)
    (originalCofactorCovectorFamily_estimate parameters length rho epsilon base low).actualCoherent lower positive bounded
  let radialXi := originalRadialVectorCurves (originalInverseRadiusCurves lower positive xi)
  let cofactor := radialXi.matrixAction parameters (originalCofactorFamily parameters length epsilon base)
    (originalCofactorFamily_estimate parameters length rho epsilon base low).actualCoherent lower positive bounded
  ⟨_,(originalRadialCovectorCurves covector).add (originalTangentialCovectorCurves cofactor)⟩

theorem originalRawFluxCurves_fullField (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (originalRawFluxCurves parameters length rho epsilon base small lower positive bounded vector xi).2.fullField bounded (radius,angles) =
      originalPhysicalRawFlux parameters length epsilon base ⟨radius,positive.le.trans inside.1,inside.2⟩
        (fun angles => vector.fullField bounded (radius,angles)) (fun angles => xi.fullField bounded (radius,angles)) angles := by
  dsimp only [originalRawFluxCurves]
  rw [SmoothLowPhysicalRow.fullField_add _ bounded _ radius inside angles,
    originalRadialCovectorCurves_fullField _ bounded radius inside angles,
    originalTangentialCovectorCurves_fullField _ bounded radius inside angles,
    SmoothLowPhysicalRow.fullField_matrixAction, SmoothLowPhysicalRow.fullField_matrixAction]
  have radialSame : (fun query => (originalRadialVectorCurves
      (originalInverseRadiusCurves lower positive xi)).fullField bounded (radius,query)) =
      (fun query => originalPolarRadialVector ((radius : ℂ)⁻¹ • xi.fullField bounded (radius,query)) query.1) := by
    funext query
    rw [originalRadialVectorCurves_fullField _ bounded radius inside query,
      originalInverseRadiusCurves_fullField lower positive xi bounded radius inside query]
  unfold originalPhysicalRawFlux
  rw [radialSame]
  all_goals exact inside

end Grad.OriginalKernelGraphRestriction
