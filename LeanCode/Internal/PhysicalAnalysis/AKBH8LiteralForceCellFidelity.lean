import AKBH7ActualForceCorrectionMoments

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualForceMoments
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

/-- Literal three-row original force correction, with complete coefficient
mixing before the axial Fourier coefficient is selected. -/
def polarForceCorrectionCell (cell : ℤ) (point : SpatialPlane) : ComplexEuclidean 3 :=
  forceCorrectionMap length (matrixFluxCell parameters (forceMatrixFamily parameters length epsilon base)
    (forceMatrixFamily_coherent parameters length rho epsilon base small) lower positive bounded cofinal
    (fun index => cartesianCovariantRow (lower index) (rows index))
    (fun index => (curves index).cartesianCovariant) cell point)

include compatible in
theorem polarForceCorrectionCell_actual (nonzero : length ≠ 0) (cell : ℤ) (index : ℕ)
    (radius : ℝ) (inside : radius ∈ Icc (lower index) 1) (polar : ℝ) :
    polarForceCorrectionCell parameters length rho epsilon base small lower positive bounded cofinal rows curves cell
      (spatialPlaneOfPair (polarCoord.symm (radius,polar))) =
      angularCoefficient (fun axial =>
        let matrix := rotatedPhysicalFrameMatrix parameters 1 1 epsilon base axial
          (polarClosedPoint radius polar ((positive index).le.trans inside.1) inside.2)
        let physical := ((curves index).physicalUFromPolar parameters length rho epsilon base small
          (lower index) (positive index) (bounded index)).fullField (bounded index) (radius,polar,axial)
        WithLp.toLp 2 ![2 * (matrix.transpose.mulVec physical) 0,
          2 * (matrix.transpose.mulVec physical) 1,-2 * (matrix.transpose.mulVec physical) 2]) cell := by
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
  have nativeCoefficient := (matrixFluxCell_actual parameters family coherent lower positive bounded cofinal decreasing
    (fun index => cartesianCovariantRow (lower index) (rows index)) (fun index => (curves index).cartesianCovariant)
    (cartesianCovariantRows_compatible lower decreasing rows compatible) cell index radius inside polar).trans
      (congrArg (fun function : ℝ → ComplexEuclidean 3 => angularCoefficient function cell) (funext productSame))
  have continuousNative : Continuous (fun axial => native.fullField (bounded index) (radius,polar,axial)) :=
    (native.fullField_continuous_angles (bounded index) radius inside).comp (continuous_const.prodMk continuous_id)
  change forceCorrectionMap length (matrixFluxCell parameters family coherent lower positive bounded cofinal _ _ cell _) = _
  rw [nativeCoefficient,← angularCoefficient_valueMap (forceCorrectionMap length) _ continuousNative cell]
  apply congrArg (fun function : ℝ → ComplexEuclidean 3 => angularCoefficient function cell)
  funext axial
  change forceCorrectionMap length (native.fullField (bounded index) (radius,polar,axial)) = _
  rw [sameForceMatrixCurves_sameU parameters length rho epsilon base small (lower index) (positive index)
    (bounded index) (curves index) radius inside (polar,axial)]
  exact forceCorrectionMap_matrix length nonzero _ _

end Grad.ActualForceMoments
