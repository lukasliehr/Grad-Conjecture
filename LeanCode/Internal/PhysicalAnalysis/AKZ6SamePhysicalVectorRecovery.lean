import AKZ5ActualMatrixBulkAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.ActualPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.BoundaryKernelAction Grad.AnnularRestriction
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation

def physicalUActionConstant (parameters : PhaseParameters) (length : ℝ) (power : ℕ) : ℝ :=
  physicalMatrixKernelConstant parameters 3 3 power *
    ((originalInverseTransposeProfile parameters length).fixed (power + 1) +
      (originalInverseTransposeProfile parameters length).deviation (power + 1))

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
include small

theorem originalInverseTransposeFamily_norm_bound (grade : ℕ) :
    ‖originalInverseTransposeFamily parameters length epsilon base grade‖ ≤
      ((originalInverseTransposeProfile parameters length).fixed grade +
        (originalInverseTransposeProfile parameters length).deviation grade) *
          (1 + physicalBudget parameters base rho epsilon (grade + 4)) := by
  let estimate := originalInverseTransposeFamily_estimate parameters length rho epsilon base small
  have fixedNonnegative := estimate.fixedNonnegative grade
  have deviationNonnegative := estimate.deviationNonnegative grade
  have budgetNonnegative := physicalBudget_nonnegative parameters base rho epsilon (grade + 4)
  have deviation := estimate.deviationBound grade
  rw [show 4 + grade = grade + 4 by omega] at deviation
  have reference := estimate.referenceBound grade
  have triangle := norm_add_le
    (originalInverseTransposeFamily parameters length epsilon base grade -
      transposeFamily (unitDiskAdmissible parameters)
        (constantFamily 1 parameters.sigma0 parameters.gamma 1 Grad.GaugeCoefficients.Physical.Frame.referenceFrame) grade)
    (transposeFamily (unitDiskAdmissible parameters)
      (constantFamily 1 parameters.sigma0 parameters.gamma 1 Grad.GaugeCoefficients.Physical.Frame.referenceFrame) grade)
  rw [sub_add_cancel] at triangle
  nlinarith only [triangle,deviation,reference,fixedNonnegative,deviationNonnegative,budgetNonnegative]

/-- Physical U is reconstructed by the actual original F^-T multiplication
kernel, with the same weighted input and output grade. -/
def physicalUFromCovariant (power : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) :
    DivisionRow 3 lower →L[ℂ] DivisionRow 3 lower :=
  originalMatrixBulkAction parameters (originalInverseTransposeFamily parameters length epsilon base)
    (originalInverseTransposeFamily_coherent parameters length rho epsilon base small) power lower positive bounded

theorem physicalUFromCovariant_bound (power : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (covariant : DivisionRow 3 lower) :
    ‖physicalUFromCovariant parameters length rho epsilon base small power lower positive bounded covariant‖ ≤
      physicalUActionConstant parameters length power *
        (1 + physicalBudget parameters base rho epsilon (power + 5)) * ‖covariant‖ := by
  have actual := originalMatrixBulkAction_bound parameters (originalInverseTransposeFamily parameters length epsilon base)
    (originalInverseTransposeFamily_coherent parameters length rho epsilon base small) power lower positive bounded covariant
  have coefficient := originalInverseTransposeFamily_norm_bound parameters length rho epsilon base small (power + 1)
  have payment := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left coefficient (physicalMatrixKernelConstant_nonnegative parameters 3 3 power)) (norm_nonneg covariant)
  rw [show power + 1 + 4 = power + 5 by omega] at payment
  apply actual.trans
  exact payment.trans_eq (by unfold physicalUActionConstant; ring)

theorem physicalUFromCovariant_restriction (power : ℕ) (lower upper : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (bounded : upper ≤ 1) (included : lower ≤ upper)
    (covariant : DivisionRow 3 lower) :
    originalBulkRestriction 3 lower upper included
      (physicalUFromCovariant parameters length rho epsilon base small power lower lowerPositive (included.trans bounded) covariant) =
      physicalUFromCovariant parameters length rho epsilon base small power upper upperPositive bounded
        (originalBulkRestriction 3 lower upper included covariant) :=
  originalMatrixBulkAction_restriction parameters (originalInverseTransposeFamily parameters length epsilon base)
    (originalInverseTransposeFamily_coherent parameters length rho epsilon base small) power lower lowerPositive (included.trans bounded)
    upper upperPositive bounded included covariant

end Grad.ActualPhysicalField
