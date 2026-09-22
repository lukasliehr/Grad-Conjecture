import AJG1ActualBulkTraceCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.AnnularPhysicalReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularReconstruction
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.PhaseAlgebra Grad.AnnularKernelL2

theorem bulkPhase_decode (parameters : PhaseParameters) (radius : RadialPoint) (shift mode : ℤ × ℤ) :
    (Real.exp (radialPhase parameters radius.val mode.2) : ℂ)⁻¹ *
      (bulkWeightRatio parameters 0 radius.val shift mode : ℂ) =
      (Real.exp (radialPhase parameters radius.val (twoFrequencyTranslation shift mode).2) : ℂ)⁻¹ := by
  rw [bulkWeightRatio, pow_zero, pow_zero, mul_one, div_one, Real.exp_sub]
  push_cast
  field_simp [(Real.exp_pos (radialPhase parameters radius.val mode.2)).ne',
    (Real.exp_pos (radialPhase parameters radius.val (twoFrequencyTranslation shift mode).2)).ne']

/-- The actual bulk kernel has the original unweighted Fourier convolution
after removing precisely its stored radial analytic phase. -/
theorem bulkKernelAction_decoded_hasSum {source target : ℕ} (parameters : PhaseParameters)
    (radius : RadialPoint) (kernel : RadialKernel parameters radius source target)
    (field : CellL2 source) (mode : ℤ × ℤ) :
    HasSum (fun shift => kernel.entry shift (twoFrequencyTranslation shift mode)
      ((Real.exp (radialPhase parameters radius.val (twoFrequencyTranslation shift mode).2) : ℂ)⁻¹ •
        field (twoFrequencyTranslation shift mode)))
      ((Real.exp (radialPhase parameters radius.val mode.2) : ℂ)⁻¹ •
        bulkKernelAction parameters 0 radius kernel field mode) := by
  have summed := ((Real.exp (radialPhase parameters radius.val mode.2) : ℂ)⁻¹ •
    ContinuousLinearMap.id ℂ (ComplexEuclidean target)).hasSum
      (bulkKernelAction_coordinate parameters 0 radius kernel field mode)
  apply summed.congr_fun
  intro shift
  symm
  change (Real.exp (radialPhase parameters radius.val mode.2) : ℂ)⁻¹ •
      ((bulkWeightRatio parameters 0 radius.val shift mode : ℂ) •
        kernel.entry shift (twoFrequencyTranslation shift mode) (field (twoFrequencyTranslation shift mode))) = _
  rw [map_smul, smul_smul, bulkPhase_decode]

/-- The half-trace realization intertwines the SAME two already completed
kernel actions. It is not an identification of their different stored weights. -/
theorem bulkNegativeLift_kernel {source target : ℕ} (parameters : PhaseParameters)
    (radius : RadialPoint) (kernel : RadialKernel parameters radius source target) (field : CellL2 source) :
    bulkNegativeLift parameters radius target (bulkKernelAction parameters 0 radius kernel field) =
      fullNegativeKernelAction (radialKernelParameters parameters radius) 0 0 kernel
        (bulkNegativeLift parameters radius source field) := by
  apply NegativeTrace.ext_coefficient (radialKernelParameters parameters radius) 0 0
  intro mode
  rw [bulkNegativeLift_coefficient]
  have left := bulkKernelAction_decoded_hasSum parameters radius kernel field mode
  have right := fullNegativeKernelAction_coefficient_hasSum (radialKernelParameters parameters radius) 0 0
    kernel (bulkNegativeLift parameters radius source field) mode
  simp only [bulkNegativeLift_coefficient] at right
  exact left.unique right

end Grad.AnnularPhysicalReconstruction
