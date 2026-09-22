import AKBC1OriginalCovariantCurves
import AKAC26ExactOriginalPhysicalRecovery

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra Grad.SourceCollarFullSource
open Grad.AnnularReconstruction Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.OriginalKernelGraphRestriction Grad.OriginalKernelRetainedDecay Grad.ActualPhysicalField
open Grad.SourceCollar Grad.AnnularKernelL2 Grad.ActualCurrentPrimitives Grad.AnnularCurrentEnergy
open Grad.BoundaryKernelAction

def originalPolarCovariantValue (angle : ℝ) (value : ComplexEuclidean 3) : ComplexEuclidean 3 :=
  WithLp.toLp 2 ((polarDomainMatrix angle).transpose.mulVec value)

def originalPolarFromCartesianCurves {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row) :=
  (((originalRadialCovectorCurves curves).bulkUnit (0 : Fin 3) 0).add
    ((originalTangentialCovectorCurves curves).bulkUnit (1 : Fin 3) 0)).add (curves.bulkUnit (2 : Fin 3) 2)

theorem originalPolarFromCartesianCurves_fullField {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower<1) (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (originalPolarFromCartesianCurves curves).fullField bounded (radius,angles) =
      originalPolarCovariantValue angles.1 (curves.fullField bounded (radius,angles)) := by
  unfold originalPolarFromCartesianCurves
  rw [SmoothLowPhysicalRow.fullField_add _ bounded _ radius inside angles,
    SmoothLowPhysicalRow.fullField_add _ bounded _ radius inside angles]
  simp_rw [SmoothLowPhysicalRow.fullField_bulkUnit _ bounded _ _ radius inside angles]
  rw [originalRadialCovectorCurves_fullField curves bounded radius inside angles,
    originalTangentialCovectorCurves_fullField curves bounded radius inside angles]
  apply PiLp.ext
  intro component
  fin_cases component <;>
    simp [originalPolarCovariantValue,originalPolarRadialValue,originalPolarTangentialValue,
      polarDomainMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_three,physicalRadialVector,
      physicalTangentialVector,physicalToroidalVector,matrixUnit_apply,operatorBasis]
  all_goals ring

theorem originalPolarCovariantValue_inverse (angle : ℝ) (value : ComplexEuclidean 3) :
    cartesianCovariantValue angle (originalPolarCovariantValue angle value)=value := by
  change WithLp.toLp 2 (Matrix.mulVec _ (Matrix.mulVec _ value))=value
  rw [Matrix.mulVec_mulVec,(polarDomainMatrix_orthogonal angle).2,Matrix.one_mulVec]

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 6≤originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (vector : ACore parameters 3)

/-- Same actual physical polar covariant a=Q^T F^T U, with every original
weighted smooth grade constructed from the original Cartesian field. -/
def originalPolarCovariantCurves :=
  originalPolarFromCartesianCurves
    (originalCartesianCovariantCurves parameters length rho epsilon base small lower positive bounded vector)

theorem originalPolarCovariantCurves_fullField (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (originalPolarCovariantCurves parameters length rho epsilon base small lower positive bounded vector).fullField bounded (radius,angles) =
      originalPolarCovariantValue angles.1
        (WithLp.toLp 2 ((originalPhysicalFrameMatrix parameters length epsilon base angles.2
          (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2)).transpose.mulVec
            (originalCoreCircle parameters vector ⟨radius,positive.le.trans inside.1,inside.2⟩ angles))) := by
  unfold originalPolarCovariantCurves
  rw [originalPolarFromCartesianCurves_fullField _ bounded radius inside angles,
    originalCartesianCovariantCurves_fullField parameters length rho epsilon base small lower positive bounded vector radius inside angles]

/-- Applying the immutable original inverse frame to this constructed
covariant returns precisely the original U at every closed collar point. -/
theorem originalPolarCovariantCurves_recovers_U (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    ((originalPolarCovariantCurves parameters length rho epsilon base small lower positive bounded vector).physicalUFromPolar
      parameters length rho epsilon base small lower positive bounded).fullField bounded (radius,angles) =
      originalCoreCircle parameters vector ⟨radius,positive.le.trans inside.1,inside.2⟩ angles := by
  rw [SmoothLowPhysicalRow.fullField_physicalUFromPolar parameters length rho epsilon base small lower positive bounded _ radius inside angles,
    originalPolarCovariantCurves_fullField parameters length rho epsilon base small lower positive bounded vector radius inside angles,
    originalPolarCovariantValue_inverse]
  change WithLp.toLp 2 (Matrix.mulVec _ (Matrix.mulVec _ _)) = _
  rw [Matrix.mulVec_mulVec,(originalInverseTransposeFamily_two_sided parameters length rho epsilon base small 0 angles.2
    (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2)).2,Matrix.one_mulVec]

end Grad.OriginalKernelCovariantRecovery
