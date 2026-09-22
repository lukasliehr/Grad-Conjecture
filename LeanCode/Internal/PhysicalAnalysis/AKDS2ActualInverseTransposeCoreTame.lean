import AKDS1ActualInverseTransposeProfile
import AKDP16ActualOriginalMatrixTame

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.ActualPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollar
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.CartesianStartup Grad.NonlinearProduct Grad.ActualOriginalSourceMoments
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- Actual original F^-T recovery, with one same image core at all orders.
The tame constants precede the state and input, and preserve original width. -/
theorem actualOriginalInverseTranspose_core_tame (parameters : PhaseParameters) (length : ℝ) :
    ∃ constants : ℕ → ℝ,(∀ grade,0≤constants grade) ∧
    ∀ (baseField : ACore parameters 3) (rho epsilon : ℝ)
      (small : physicalBudget parameters baseField rho epsilon 6≤originalCoefficientLowRadius parameters length)
      (covariant : ACore parameters 3),
      ∃ vector : ACore parameters 3,
        (originalSourceMoments parameters vector).field =
          originalMatrixKernel (unitDiskAdmissible parameters)
            (originalInverseTransposeFamily parameters length epsilon baseField)
            (originalInverseTransposeFamily_coherent parameters length rho epsilon baseField small)
            (originalSourceMoments parameters covariant).field ∧
        ∀ grade,originalGradeNorm grade vector ≤ constants grade *
          (originalGradeNorm grade covariant +
            (1+physicalBudget parameters baseField rho epsilon (4+grade))*originalGradeNorm 0 covariant) := by
  obtain ⟨constants,nonnegative,bounds⟩ := startupOriginalMatrix_core_tame parameters
    (unitDiskAdmissible parameters) one_ne_zero one_ne_zero 4
    (originalInverseTransposeAbsoluteProfile parameters length)
    (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)
  refine ⟨constants,nonnegative,?_⟩
  intro baseField rho epsilon small covariant
  exact bounds 3 3 baseField rho epsilon
    (originalInverseTransposeFamily parameters length epsilon baseField)
    (transposeFamily (unitDiskAdmissible parameters)
      (constantFamily 1 parameters.sigma0 parameters.gamma 1 Grad.GaugeCoefficients.Physical.Frame.referenceFrame))
    (originalInverseTransposeFamily_absoluteEstimate parameters length rho epsilon baseField small)
    covariant (originalCoefficient_low_margin parameters length rho epsilon baseField small).2.1

end Grad.ActualPhysicalField
