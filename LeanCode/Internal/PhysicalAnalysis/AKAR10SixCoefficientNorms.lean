import AKAR9ActualSixCircleCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.SourceBoundaryTrace Grad.SourceCollarDivision
open Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.PhaseAlgebra Grad.BoundaryLift
open Grad.SourceCollarCoefficients Grad.ActualPhysicalField Grad.SourceCollar
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Envelope

structure AxisCirclePrimitives.Bounded (primitives : AxisCirclePrimitives) (constant : ℝ) : Prop where
  frameTranspose : ‖primitives.frameTranspose‖ ≤ constant
  rotationFrameTranspose : ‖primitives.rotationFrameTranspose‖ ≤ constant
  covector : ‖primitives.covector‖ ≤ constant
  rotationCovector : ‖primitives.rotationCovector‖ ≤ constant
  cofactor : ‖primitives.cofactor‖ ≤ constant
  rotationCofactor : ‖primitives.rotationCofactor‖ ≤ constant

structure AxisCircleCoefficients.Bounded (coefficients : AxisCircleCoefficients) (constant : ℝ) : Prop where
  c : ‖coefficients.c‖ ≤ constant
  d : ‖coefficients.d‖ ≤ constant
  C : ‖coefficients.C‖ ≤ constant
  RC : ‖coefficients.RC‖ ≤ constant
  kappa : ‖coefficients.kappa‖ ≤ constant
  Rkappa : ‖coefficients.Rkappa‖ ≤ constant

def originalAxisMatrixConstant (parameters : PhaseParameters) (length : ℝ) : ℝ :=
  max (max (originalCircleFamilyConstant parameters 3 3 (originalTransposeFrameProfile parameters length) false)
    (originalCircleFamilyConstant parameters 3 3 (originalTransposeFrameProfile parameters length) true))
  (max (max (originalCircleFamilyConstant parameters 3 3 (originalCofactorCovectorProfile parameters length) false)
    (originalCircleFamilyConstant parameters 3 3 (originalCofactorCovectorProfile parameters length) true))
    (max (originalCircleFamilyConstant parameters 3 3 (originalCofactorProfile parameters length) false)
      (originalCircleFamilyConstant parameters 3 3 (originalCofactorProfile parameters length) true)))

theorem originalAxisCirclePrimitives_bounded (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (base : ACore parameters 3) (small : physicalBudget parameters base rho epsilon 8 ≤ originalCoefficientLowRadius parameters length)
    (radius : RadialPoint) :
    (originalAxisCirclePrimitives parameters length rho epsilon base small radius).Bounded
      (originalAxisMatrixConstant parameters length) := by
  have margin := originalAxis_primitive_margin parameters length rho epsilon base small
  have frame := originalTransposeFrameFamily_estimate parameters length rho epsilon base margin.1
  have covector := originalCofactorCovectorFamily_estimate parameters length rho epsilon base margin.1
  have cofactor := originalCofactorFamily_estimate parameters length rho epsilon base margin.1
  constructor
  · exact (originalCircleFamilyAction_norm parameters rho epsilon base _ _ _ frame margin.2 radius).trans
      ((le_max_left _ _).trans (le_max_left _ _))
  · exact (originalCircleFamilyAngularAction_norm parameters rho epsilon base _ _ _ frame margin.2 radius).trans
      ((le_max_right _ _).trans (le_max_left _ _))
  · exact (originalCircleFamilyAction_norm parameters rho epsilon base _ _ _ covector margin.2 radius).trans
      ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _)))
  · exact (originalCircleFamilyAngularAction_norm parameters rho epsilon base _ _ _ covector margin.2 radius).trans
      ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _)))
  · exact (originalCircleFamilyAction_norm parameters rho epsilon base _ _ _ cofactor margin.2 radius).trans
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  · exact (originalCircleFamilyAngularAction_norm parameters rho epsilon base _ _ _ cofactor margin.2 radius).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

theorem AxisCirclePrimitives.Bounded.coefficients {primitives : AxisCirclePrimitives} {constant : ℝ}
    (bounded : primitives.Bounded constant) (parameters : PhaseParameters) :
    (primitives.coefficients parameters).Bounded (12 * constant) := by
  have nonnegative : 0 ≤ constant := (norm_nonneg _).trans bounded.cofactor
  have rowBound (row : CellL2 3 →L[ℂ] CellL2 1) (rowBound : ‖row‖ ≤ 2)
      (matrix : CellL2 3 →L[ℂ] CellL2 3) (matrixBound : ‖matrix‖ ≤ constant) :
      ‖row.comp matrix‖ ≤ 2*constant :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul rowBound matrixBound (norm_nonneg _) (by norm_num))
  have sandwich (row : CellL2 3 →L[ℂ] CellL2 1) (rowBound : ‖row‖ ≤ 2)
      (matrix : CellL2 3 →L[ℂ] CellL2 3) (matrixBound : ‖matrix‖ ≤ constant)
      (column : CellL2 1 →L[ℂ] CellL2 3) (columnBound : ‖column‖ ≤ 2) :
      ‖row.comp (matrix.comp column)‖ ≤ 4*constant := by
    have inner := (ContinuousLinearMap.opNorm_comp_le matrix column).trans
      (mul_le_mul matrixBound columnBound (norm_nonneg _) nonnegative)
    have outer := (ContinuousLinearMap.opNorm_comp_le row (matrix.comp column)).trans
      (mul_le_mul rowBound inner (norm_nonneg _) (by norm_num))
    nlinarith only [outer]
  have radial := originalCircleRadialRow_norm parameters
  have tangential := originalCircleTangentialRow_norm parameters
  have radialColumn := originalCircleRadialColumn_norm parameters
  have tangentialColumn := originalCircleTangentialColumn_norm parameters
  constructor
  · exact (rowBound _ tangential _ bounded.frameTranspose).trans (by nlinarith)
  · exact ((norm_sub_le _ _).trans (add_le_add (rowBound _ tangential _ bounded.rotationFrameTranspose)
      (rowBound _ radial _ bounded.frameTranspose))).trans (by nlinarith)
  · exact (rowBound _ radial _ bounded.covector).trans (by nlinarith)
  · exact ((norm_add_le _ _).trans (add_le_add (rowBound _ tangential _ bounded.covector)
      (rowBound _ radial _ bounded.rotationCovector))).trans (by nlinarith)
  · exact (sandwich _ tangential _ bounded.cofactor _ radialColumn).trans (by nlinarith)
  · have one := sandwich _ radial _ bounded.cofactor _ radialColumn
    have two := sandwich _ tangential _ bounded.rotationCofactor _ radialColumn
    have three := sandwich _ tangential _ bounded.cofactor _ tangentialColumn
    change ‖-_+_+_‖ ≤ _
    apply ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    rw [norm_neg]
    linarith

/-- Uniform six-coefficient bounds at the original analytic width; no radial
weight or total angular H1 norm is substituted for the original Wλ circle norm. -/
theorem originalAxisCircleCoefficients_bounded (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (base : ACore parameters 3) (small : physicalBudget parameters base rho epsilon 8 ≤ originalCoefficientLowRadius parameters length)
    (radius : RadialPoint) :
    (originalAxisCircleCoefficients parameters length rho epsilon base small radius).Bounded
      (12 * originalAxisMatrixConstant parameters length) :=
  (originalAxisCirclePrimitives_bounded parameters length rho epsilon base small radius).coefficients parameters

end Grad.OriginalKernelRetainedDecay
