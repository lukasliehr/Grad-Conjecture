import AKBC39SameNegativeCurveActions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set
open scoped BigOperators
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.OriginalKernelRetainedDecay
open Grad.SourceCollarFullSource Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Envelope Grad.SourceCollar Grad.ActualPhysicalField
open Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.ActualPolarFlux

theorem originalPolarCofactorRow_value (angle : ℝ) (matrix : Matrix (Fin 3) (Fin 3) ℂ) (value : ComplexEuclidean 3) :
    (∑ component : Fin 3,polarMatrixEntry 0 component angle matrix • matrixUnit (0 : Fin 1) component value)=
      originalPolarRadialValue (WithLp.toLp 2 (matrix.mulVec (cartesianCovariantValue angle value))) angle := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  simp [polarMatrixEntry,polarVector,matrixPairing,cartesianCovariantValue,polarDomainMatrix,
    originalPolarRadialValue,Matrix.mulVec,Matrix.mul_apply,dotProduct,Fin.sum_univ_three,
    physicalRadialVector,physicalTangentialVector,physicalToroidalVector,matrixUnit_apply,operatorBasis]
  ring

theorem originalPolarCofactorComponent_value (angle : ℝ) (matrix : Matrix (Fin 3) (Fin 3) ℂ) (value : ComplexEuclidean 1) :
    polarMatrixEntry 1 0 angle matrix • value=
      originalPolarTangentialValue (WithLp.toLp 2 (matrix.mulVec (originalPolarRadialVector value angle))) angle := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  simp [polarMatrixEntry,polarVector,matrixPairing,originalPolarRadialVector,originalPolarTangentialValue,
    Matrix.mulVec,dotProduct,Fin.sum_univ_three,physicalRadialVector,physicalTangentialVector,matrixUnit_apply,operatorBasis]
  ring

theorem originalCofactorCovectorFamily_product (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 6≤originalCoefficientLowRadius parameters length)
    (axial : ℝ) (point : ClosedDisk) :
    familyMatrix (originalCofactorCovectorFamily parameters length epsilon base) 0 axial point=
      originalPhysicalSignedCofactor parameters length epsilon base axial point *
        (originalPhysicalFrameMatrix parameters length epsilon base axial point).transpose := by
  change familyMatrix (composeFamily (unitDiskAdmissible parameters)
    (originalCofactorFamily parameters length epsilon base)
    (originalTransposeFrameFamily parameters length epsilon base)) 0 axial point=_
  rw [familyMatrix_comp (unitDiskAdmissible parameters) _ _
    (originalCofactorFamily_estimate parameters length rho epsilon base small).actualCoherent
    (originalTransposeFrameFamily_estimate parameters length rho epsilon base small).actualCoherent,
    originalCofactorFamily_matrix parameters length rho epsilon base small,
    originalTransposeFrameFamily_matrix parameters length rho epsilon base small,
    originalInverseFamily_eq_matrixInverse parameters length rho epsilon base small]
  rfl

theorem originalSignedFlux_sameRaw (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 6≤originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (vector : ACore parameters 3)
    (radius : Icc lower (1 : ℝ)) (xi : ℝ×ℝ→ComplexEuclidean 1) (angles : ℝ×ℝ) :
    (∑ component : Fin 3,originalSignedCofactorRow parameters length epsilon base 0 angles.2 angles.1
      (polarClosedPoint radius.val angles.1 (positive.le.trans radius.property.1) radius.property.2) component •
      matrixUnit (0 : Fin 1) component
        ((originalPolarCovariantCurves parameters length rho epsilon base small lower positive bounded vector).fullField bounded (radius.val,angles)))+
    originalSignedCofactorRow parameters length epsilon base 0 angles.2 angles.1
      (polarClosedPoint radius.val angles.1 (positive.le.trans radius.property.1) radius.property.2) 1 •
        ((radius.val : ℂ)⁻¹ • xi angles)=
    originalPhysicalRawFlux parameters length epsilon base (tupleRadius lower positive radius)
      (originalCoreCircle parameters vector (tupleRadius lower positive radius)) xi angles := by
  simp only [originalSignedCofactorRow]
  rw [originalPolarCofactorRow_value,
    originalPolarCovariantCurves_fullField parameters length rho epsilon base small lower positive bounded vector radius.val radius.property angles,
    originalPolarCovariantValue_inverse,
    polarMatrixEntry_symmetric 0 1 angles.1 _
      (originalPhysicalSignedCofactor_symmetric parameters length epsilon base angles.2 _),
    originalPolarCofactorComponent_value]
  unfold originalPhysicalRawFlux
  rw [physicalMatrixProduct_apply,physicalMatrixProduct_apply,
    originalCofactorCovectorFamily_product parameters length rho epsilon base small,
    originalCofactorFamily_matrix parameters length rho epsilon base small,
    originalInverseFamily_eq_matrixInverse parameters length rho epsilon base small,Matrix.mulVec_mulVec]
  rfl

end Grad.OriginalKernelCovariantRecovery
