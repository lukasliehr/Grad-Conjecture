import AKBK7OriginalForceAngularContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualCartesianWeakEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.ActualSmoothPhysicalField Grad.ActualPhysicalField Grad.ActualCartesianDescent Grad.ActualCartesianFlux
open Grad.AnnularRestriction Grad.DiskExtension.Operator Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Ledger Grad.ActualCurrentPrimitives

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℕ → ℝ) (positive : ∀ index, 0 < lower index) (bounded : ∀ index, lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index, DivisionRow 3 (lower index))
    (curves : ∀ index, SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction 3 (lower second) (lower first) (decreasing ordered) (rows second) = rows first)

open Grad.ActualForceMoments Grad.Constraints.Gauges
include compatible

/-- The complete force matrix acts before the SAME axial cell is selected. -/
theorem nativeForceMatrixCell_actual (cell : ℤ) (index : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc (lower index) 1) (polar : ℝ) :
    matrixFluxCell parameters (forceMatrixFamily parameters length epsilon base)
      (forceMatrixFamily_coherent parameters length rho epsilon base small) lower positive bounded cofinal
      (fun index => cartesianCovariantRow (lower index) (rows index)) (fun index => (curves index).cartesianCovariant)
      cell (spatialPlaneOfPair (polarCoord.symm (radius,polar))) =
      angularCoefficient (fun axial => (sameForceMatrixCurves parameters length rho epsilon base small
        (lower index) (positive index) (bounded index) (curves index)).fullField (bounded index) (radius,polar,axial)) cell := by
  let family := forceMatrixFamily parameters length epsilon base
  have coherent := forceMatrixFamily_coherent parameters length rho epsilon base small
  let native := sameForceMatrixCurves parameters length rho epsilon base small (lower index) (positive index) (bounded index) (curves index)
  have productSame (axial : ℝ) :
      WithLp.toLp 2 ((familyMatrix family 0 axial
        (polarClosedPoint radius polar ((positive index).le.trans inside.1) inside.2)).mulVec
          ((curves index).cartesianCovariant.fullField (bounded index) (radius,polar,axial))) =
      native.fullField (bounded index) (radius,polar,axial) := by
    exact (((curves index).cartesianCovariant.fullField_matrixAction parameters family coherent
      (lower index) (positive index) (bounded index) radius inside (polar,axial)).trans
        (physicalMatrixProduct_apply parameters family radius ((positive index).le.trans inside.1) inside.2 _ (polar,axial))).symm
  exact (matrixFluxCell_actual parameters family coherent lower positive bounded cofinal decreasing
    (fun index => cartesianCovariantRow (lower index) (rows index)) (fun index => (curves index).cartesianCovariant)
    (cartesianCovariantRows_compatible lower decreasing rows compatible) cell index radius inside polar).trans
      (congrArg (fun function : ℝ → ComplexEuclidean 3 => angularCoefficient function cell) (funext productSame))

omit compatible in
private theorem forceCorrectionMap_planar (value : ComplexEuclidean 3) :
    planarPartMap (forceCorrectionMap length value) = planarPartMap ((2 : ℂ) • value) := by
  rw [forceCorrectionMap_apply]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [planarPartMap,PiLp.smul_apply]

/-- Exact planar correction for the original force algebra; the distinct
third normalization remains in the shared correction field. -/
theorem nativeForceCorrectionCell_planar (cell : ℤ) (index : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc (lower index) 1) (polar : ℝ) :
    planarPartMap (polarForceCorrectionCell parameters length rho epsilon base small lower positive bounded cofinal rows curves cell
      (spatialPlaneOfPair (polarCoord.symm (radius,polar)))) =
      planarPartMap (angularCoefficient (fun axial => (2 : ℂ) •
        (sameForceMatrixCurves parameters length rho epsilon base small (lower index) (positive index) (bounded index) (curves index)).fullField
          (bounded index) (radius,polar,axial)) cell) := by
  rw [polarForceCorrectionCell,forceCorrectionMap_planar,
    nativeForceMatrixCell_actual parameters length rho epsilon base small lower positive bounded cofinal decreasing rows curves compatible cell index radius inside polar]
  congr 1
  exact (angularCoefficient_smul_continuous (2 : ℂ) _ cell).symm

end Grad.ActualCartesianWeakEquations
