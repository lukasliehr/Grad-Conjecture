import AKZ2ActualMatrixCoefficientMoments

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter
open scoped Topology BigOperators
namespace Grad.ActualPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.AnnularKernelContinuity Grad.BoundaryKernelAction
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation

def physicalMatrixKernelConstant (parameters : PhaseParameters) (input output moment : ℕ) : ℝ :=
  Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
    ∑ _row : Fin output, ∑ column : Fin input, coefficientFourierConstant moment 0 * ‖operatorBasis column‖

theorem physicalMatrixKernelConstant_nonnegative (parameters : PhaseParameters) (input output moment : ℕ) :
    0 ≤ physicalMatrixKernelConstant parameters input output moment :=
  mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
    (fun _ _ => mul_nonneg (coefficientFourierConstant_nonnegative _ _) (norm_nonneg _))))

variable {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family)

/-- The actual full-cell multiplication kernel of an original matrix family. -/
def originalMatrixRadialKernel (radius : RadialPoint) : RadialKernel parameters radius input output :=
  radialMatrixKernel parameters radius input output
    (fun row column => physicalMatrixScalar parameters family coherent row column 0 radius.val)
    (fun row column moment => physicalMatrixScalar_moment_summable parameters family coherent row column moment 0 radius.val
      radius.property.1 radius.property.2)

theorem originalMatrixRadialKernel_bound (radius : RadialPoint) (moment : ℕ) :
    fullKernelMoment (radialKernelParameters parameters radius) moment (originalMatrixRadialKernel parameters family coherent radius) ≤
      physicalMatrixKernelConstant parameters input output moment * ‖family (moment + 1)‖ := by
  apply (radialMatrixKernel_moment_le parameters radius input output moment _ _).trans
  have summed := Finset.sum_le_sum (s := Finset.univ) (fun row _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun column _ =>
      physicalMatrixScalar_moment_bound parameters family coherent row column moment 0 radius.val radius.property.1 radius.property.2))
  apply (mul_le_mul_of_nonneg_left summed (Real.exp_pos _).le).trans_eq
  simp only [physicalMatrixKernelConstant,Nat.add_zero]
  simp_rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro column _
  ring

theorem originalMatrixRadialKernel_regular :
    RegularKernelFamily (originalMatrixRadialKernel parameters family coherent) := by
  refine regularKernelFamily_of_bound _ ?_ _ (fun moment radius => originalMatrixRadialKernel_bound parameters family coherent radius moment)
  intro shift mode
  change Continuous (fun radius : RadialPoint => matrixMultiplicationEntry input output
    (fun row column index => physicalMatrixScalar parameters family coherent row column 0 radius.val index) shift mode)
  exact matrixMultiplicationEntry_continuous (X := RadialPoint) input output
    (fun (radius : RadialPoint) row column index => physicalMatrixScalar parameters family coherent row column 0 radius.val index)
    (fun row column index => (physicalMatrixScalar_continuous parameters family coherent row column 0 index).comp continuous_subtype_val) shift mode

end Grad.ActualPhysicalField
