import AKAR2OriginalLambdaCircleAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open scoped BigOperators
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.SourceBoundaryTrace Grad.SourceCollarDivision
open Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.PhaseAlgebra Grad.BoundaryLift
open Grad.SourceCollarCoefficients Grad.ActualPhysicalField

variable {input output : ℕ} {parameters : PhaseParameters}

def angularCoefficientEntry (kernel : FullTwoFrequencyKernel parameters input output) (shift mode : ℤ × ℤ) :
    ComplexEuclidean input →L[ℂ] ComplexEuclidean output :=
  (Complex.I * (shift.1 : ℂ)) • kernel.entry shift mode

theorem angularCoefficientEntry_bound (kernel : FullTwoFrequencyKernel parameters input output) (shift mode : ℤ × ℤ) :
    ‖angularCoefficientEntry kernel shift mode‖ ≤ annularFrequency shift.1 shift.2 * kernel.entryNorm shift := by
  apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
  simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_intCast]
  apply mul_le_mul _ (kernel.entry_le shift mode) (norm_nonneg _) (annularFrequency_pos shift).le
  unfold annularFrequency
  linarith [abs_nonneg (shift.2 : ℝ)]

theorem angularCoefficientMajorant_summable (kernel : FullTwoFrequencyKernel parameters input output) (moment : ℕ) :
    Summable (fun shift => boundaryCoefficientPhaseCost parameters shift * annularFrequency shift.1 shift.2^moment *
      (annularFrequency shift.1 shift.2 * kernel.entryNorm shift)) := by
  exact (kernel.moments (moment+1)).congr (fun shift => by rw [pow_succ]; ring)

/-- Literal Fourier derivative of the coefficient; no derivative of the
unknown field is hidden inside this kernel. -/
def angularCoefficientKernel (kernel : FullTwoFrequencyKernel parameters input output) :
    FullTwoFrequencyKernel parameters input output :=
  fullKernelOfEntries parameters (angularCoefficientEntry kernel)
    (fun shift => annularFrequency shift.1 shift.2 * kernel.entryNorm shift)
    (angularCoefficientEntry_bound kernel) (angularCoefficientMajorant_summable kernel)

theorem angularCoefficientKernel_entry (kernel : FullTwoFrequencyKernel parameters input output) (shift mode : ℤ × ℤ) :
    (angularCoefficientKernel kernel).entry shift mode = (Complex.I * (shift.1 : ℂ)) • kernel.entry shift mode := rfl

theorem angularCoefficientKernel_moment (kernel : FullTwoFrequencyKernel parameters input output) (moment : ℕ) :
    fullKernelMoment parameters moment (angularCoefficientKernel kernel) ≤ fullKernelMoment parameters (moment+1) kernel := by
  apply ((angularCoefficientKernel kernel).moments moment).tsum_le_tsum _ (kernel.moments (moment+1))
  intro shift
  have entry := fullKernelOfEntries_entryNorm_le parameters (angularCoefficientEntry kernel)
    (fun shift => annularFrequency shift.1 shift.2 * kernel.entryNorm shift)
    (angularCoefficientEntry_bound kernel) (angularCoefficientMajorant_summable kernel) shift
  have paid := mul_le_mul_of_nonneg_left entry
    (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative parameters shift) (pow_nonneg (annularFrequency_pos shift).le moment))
  change _ ≤ _ at paid
  exact paid.trans_eq (by rw [pow_succ]; ring)

theorem originalMatrix_lambdaCircle_bound (parameters : PhaseParameters)
    (family : Grad.GaugeCoefficients.Physical.Allocation.CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : Grad.GaugeCoefficients.Physical.Allocation.FamilyCoherent family)
    (radius : RadialPoint) (field : CellL2 input) :
    ‖lambdaCircleAction parameters radius (originalMatrixRadialKernel parameters family coherent radius) field‖ ≤
      (2 * physicalMatrixKernelConstant parameters input output 1 * ‖family 2‖) * ‖field‖ := by
  apply (lambdaCircleAction_bound parameters radius _ field).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg field)
  have bound := originalMatrixRadialKernel_bound parameters family coherent radius 1
  nlinarith only [bound]

theorem originalMatrix_angular_lambdaCircle_bound (parameters : PhaseParameters)
    (family : Grad.GaugeCoefficients.Physical.Allocation.CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : Grad.GaugeCoefficients.Physical.Allocation.FamilyCoherent family)
    (radius : RadialPoint) (field : CellL2 input) :
    ‖lambdaCircleAction parameters radius (angularCoefficientKernel (originalMatrixRadialKernel parameters family coherent radius)) field‖ ≤
      (2 * physicalMatrixKernelConstant parameters input output 2 * ‖family 3‖) * ‖field‖ := by
  apply (lambdaCircleAction_bound parameters radius _ field).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg field)
  have bound := (angularCoefficientKernel_moment (originalMatrixRadialKernel parameters family coherent radius) 1).trans
    (originalMatrixRadialKernel_bound parameters family coherent radius 2)
  nlinarith only [bound]

end Grad.OriginalKernelRetainedDecay
