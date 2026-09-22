import AKAR28ActualKernelXiIdentity
import AKAR10SixCoefficientNorms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.FinitePhysicalJetLift Grad.OriginalFlatAxisDecay
open Grad.SourceCollar Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularReconstruction

theorem originalCoreCircleTrace_flat_bound {dimension : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters dimension 4) (flat : ∀ cell, ZeroCartesianFirstJets (field.toCore.val cell))
    (radius : RadialPoint) (rotated : Bool) :
    ‖originalCoreCircleTrace parameters (if rotated then rotationCore parameters field.toCore else field.toCore) radius‖ ≤
      flatDecayConstant * radius.val^(3/2:ℝ) * ‖field‖ := by
  have equality := (originalCoreCircleTrace_represents parameters _ radius).unique
    (originalSmoothCircleTrace_represents parameters field flat radius rotated)
  rw [equality]
  exact originalSmoothCircleTrace_bound parameters field flat radius rotated

theorem originalCircle_c_minus_d_bound {coefficients : AxisCircleCoefficients} {constant : ℝ}
    (bounded : coefficients.Bounded constant) (field rotated : CellL2 3) :
    ‖coefficients.c rotated-coefficients.d field‖ ≤ constant*(‖rotated‖+‖field‖) := by
  calc
    _ ≤ ‖coefficients.c rotated‖+‖coefficients.d field‖ := norm_sub_le _ _
    _ ≤ constant*‖rotated‖+constant*‖field‖ := add_le_add
      ((coefficients.c.le_opNorm _).trans (mul_le_mul_of_nonneg_right bounded.c (norm_nonneg _)))
      ((coefficients.d.le_opNorm _).trans (mul_le_mul_of_nonneg_right bounded.d (norm_nonneg _)))
    _ = _ := by ring

def originalScalarDecayConstant (parameters : PhaseParameters) (length : ℝ) : ℝ :=
  24*originalAxisMatrixConstant parameters length*flatDecayConstant

/-- Both xi and Rxi have the exact r^(5/2) estimate in the original
L2(theta;ell2_lambda), derived from the literal original kernel equation. -/
theorem originalKernelXi_scalar_decay (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 8 ≤ originalCoefficientLowRadius parameters length)
    (state : QuotientState parameters) (sameBase : state.2.1=planarReferenceCore parameters+base)
    (vector : GradeCore parameters 3 4) (flat : ∀ cell, ZeroCartesianFirstJets (vector.toCore.val cell))
    (scalar : ACore parameters 1)
    (homogeneous : quotientRowsDerivative parameters length 1 state ![(0,vector.toCore,scalar)] = 0)
    (radius : RadialPoint) :
    ‖originalCoreCircleTrace parameters (originalKernelXi state.2.1 vector.toCore scalar) radius‖ ≤
      originalScalarDecayConstant parameters length*radius.val^(5/2:ℝ)*‖vector‖ ∧
    ‖originalCoreCircleTrace parameters (rotationCore parameters (originalKernelXi state.2.1 vector.toCore scalar)) radius‖ ≤
      originalScalarDecayConstant parameters length*radius.val^(5/2:ℝ)*‖vector‖ := by
  have bounded := originalAxisCircleCoefficients_bounded parameters length rho epsilon base small radius
  have nonnegative : 0 ≤ 12*originalAxisMatrixConstant parameters length := (norm_nonneg _).trans bounded.c
  have one := originalCoreCircleTrace_flat_bound parameters vector flat radius false
  have two := originalCoreCircleTrace_flat_bound parameters vector flat radius true
  simp only [Bool.false_eq_true,↓reduceIte] at one two
  have source := (originalCircle_c_minus_d_bound bounded
    (originalCoreCircleTrace parameters vector.toCore radius)
    (originalCoreCircleTrace parameters (rotationCore parameters vector.toCore) radius)).trans
    (mul_le_mul_of_nonneg_left (add_le_add two one) nonnegative)
  have power : radius.val*radius.val^(3/2:ℝ)=radius.val^(5/2:ℝ) := by
    calc
      _ = radius.val^(1:ℝ)*radius.val^(3/2:ℝ) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add' radius.property.1 (by norm_num : (1:ℝ)+(3/2:ℝ)≠0)]
        norm_num
  have sourcePaid : radius.val * ‖(originalAxisCircleCoefficients parameters length rho epsilon base small radius).c
      (originalCoreCircleTrace parameters (rotationCore parameters vector.toCore) radius)-
      (originalAxisCircleCoefficients parameters length rho epsilon base small radius).d
      (originalCoreCircleTrace parameters vector.toCore radius)‖ ≤
      originalScalarDecayConstant parameters length*radius.val^(5/2:ℝ)*‖vector‖ := by
    apply (mul_le_mul_of_nonneg_left source radius.property.1).trans_eq
    rw [originalScalarDecayConstant,← power]
    ring
  constructor
  · rw [originalKernelXi_circle_formula parameters length rho epsilon base small radius state sameBase vector.toCore scalar homogeneous,
      norm_smul,Complex.norm_real,Real.norm_of_nonneg radius.property.1]
    exact (mul_le_mul_of_nonneg_left
      (((originalCircleAngularInverse parameters 1).le_opNorm _).trans
        ((mul_le_mul_of_nonneg_right (originalCircleAngularInverse_norm parameters 1) (norm_nonneg _)).trans_eq (one_mul _)))
      radius.property.1).trans sourcePaid
  · rw [originalKernelXi_circle_rotation parameters length rho epsilon base small radius state sameBase vector.toCore scalar homogeneous,
      norm_smul,Complex.norm_real,Real.norm_of_nonneg radius.property.1]
    exact sourcePaid

end Grad.OriginalKernelRetainedDecay
