import AKAR31ActualOriginalFluxDerivative
import AKAR29OriginalScalarDecay

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.FinitePhysicalJetLift Grad.OriginalFlatAxisDecay
open Grad.SourceCollar Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularReconstruction

theorem originalCircleFluxRotation_bound {coefficients : AxisCircleCoefficients} {constant : ℝ}
    (bounded : coefficients.Bounded constant) (radius : RadialPoint)
    (vector rotated : CellL2 3) (xi rotatedXi : CellL2 1) :
    ‖originalCircleFluxRotation coefficients radius vector rotated xi rotatedXi‖ ≤
      constant*(‖vector‖+‖rotated‖+‖(radius.val : ℂ)⁻¹ • xi‖+‖(radius.val : ℂ)⁻¹ • rotatedXi‖) := by
  have applyBound {input : ℕ} (operator : CellL2 input →L[ℂ] CellL2 1) (bound : ‖operator‖≤constant) (field : CellL2 input) :
      ‖operator field‖≤constant*‖field‖ := (operator.le_opNorm _).trans (mul_le_mul_of_nonneg_right bound (norm_nonneg _))
  unfold originalCircleFluxRotation
  apply ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))).trans
  apply (add_le_add (add_le_add (applyBound _ bounded.RC _) (applyBound _ bounded.C _))
    (add_le_add (applyBound _ bounded.Rkappa _) (applyBound _ bounded.kappa _))).trans_eq
  ring

theorem originalCircle_divided_decay {dimension : ℕ} (radius : RadialPoint) (positive : 0<radius.val)
    (field : CellL2 dimension) (constant : ℝ) (bound : ‖field‖≤constant*radius.val^(5/2:ℝ)) :
    ‖(radius.val : ℂ)⁻¹ • field‖≤constant*radius.val^(3/2:ℝ) := by
  rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg positive.le]
  apply (mul_le_mul_of_nonneg_left bound (inv_nonneg.mpr positive.le)).trans_eq
  have power : radius.val^(5/2:ℝ)=radius.val*radius.val^(3/2:ℝ) := by
    calc
      _ = radius.val^((1:ℝ)+(3/2:ℝ)) := by norm_num
      _ = _ := by rw [Real.rpow_add positive,Real.rpow_one]
  rw [power]
  field_simp

def originalFluxDecayConstant (parameters : PhaseParameters) (length : ℝ) : ℝ :=
  (12*originalAxisMatrixConstant parameters length)*(2*flatDecayConstant+2*originalScalarDecayConstant parameters length)

theorem originalKernelPhysicalX_decay (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 8 ≤ originalCoefficientLowRadius parameters length)
    (state : QuotientState parameters) (sameBase : state.2.1=planarReferenceCore parameters+base)
    (vector : GradeCore parameters 3 4) (flat : ∀ cell, ZeroCartesianFirstJets (vector.toCore.val cell))
    (scalar : ACore parameters 1)
    (homogeneous : quotientRowsDerivative parameters length 1 state ![(0,vector.toCore,scalar)] = 0)
    (radius : RadialPoint) (positive : 0<radius.val) :
    ‖originalKernelPhysicalX parameters length rho epsilon base small radius state.2.1 vector.toCore scalar‖ ≤
      originalFluxDecayConstant parameters length*radius.val^(3/2:ℝ)*‖vector‖ := by
  have bounded := originalAxisCircleCoefficients_bounded parameters length rho epsilon base small radius
  have nonnegative : 0≤12*originalAxisMatrixConstant parameters length := (norm_nonneg _).trans bounded.c
  have one := originalCoreCircleTrace_flat_bound parameters vector flat radius false
  have two := originalCoreCircleTrace_flat_bound parameters vector flat radius true
  simp only [Bool.false_eq_true,↓reduceIte] at one two
  have scalarBounds := originalKernelXi_scalar_decay parameters length rho epsilon base small state sameBase vector flat scalar homogeneous radius
  have rearrange (field : CellL2 1) (bound : ‖field‖≤originalScalarDecayConstant parameters length*radius.val^(5/2:ℝ)*‖vector‖) :
      ‖(radius.val : ℂ)⁻¹ • field‖≤originalScalarDecayConstant parameters length*radius.val^(3/2:ℝ)*‖vector‖ := by
    have paid : ‖field‖≤(originalScalarDecayConstant parameters length*‖vector‖)*radius.val^(5/2:ℝ) := by
      convert bound using 1; ring
    have divided := originalCircle_divided_decay radius positive field _ paid
    convert divided using 1; ring
  have three := rearrange _ scalarBounds.1
  have four := rearrange _ scalarBounds.2
  apply (originalCircleFluxRotation_bound bounded radius _ _ _ _).trans
  apply (mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add one two) three) four) nonnegative).trans_eq
  unfold originalFluxDecayConstant
  ring

end Grad.OriginalKernelRetainedDecay
