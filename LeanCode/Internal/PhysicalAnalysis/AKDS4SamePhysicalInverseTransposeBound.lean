import AKDS2ActualInverseTransposeCoreTame
import AKDS3SameOriginalMatrixPhysicalField
import AKDR9ActualRetainedScalarRecoveryNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace Grad.ActualPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollar
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.CartesianStartup Grad.NonlinearProduct Grad.ActualOriginalSourceMoments
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.PDEBootstrap Grad.GenericCarriers
open Grad.OriginalVectorCoreRecovery Grad.OriginalCoreRealization

/-- The bound applies to the already recovered SAME physical vector U.
No choice of a different solution or change of the physical frame is made. -/
theorem actualOriginalInverseTranspose_sameCore_bound (parameters : PhaseParameters) (length : ℝ) :
    ∃ constants : ℕ → ℝ,(∀ grade,0≤constants grade) ∧
    ∀ (baseField : ACore parameters 3) (rho epsilon : ℝ)
      (_small : physicalBudget parameters baseField rho epsilon 6≤originalCoefficientLowRadius parameters length)
      (covariant vector : ACore parameters 3)
      (raw : ℝ × Spatial → PhysicalValue 3),
      StartupOrbitContinuous raw →
      (∀ (point : ClosedDisk),0<‖point.val‖ → ∀ axial : ℝ,
        (originalPhysicalClosedJet parameters covariant).value (point,(axial : CellCircle)) = raw (axial,point.val)) →
      (∀ (point : ClosedDisk),0<‖point.val‖ → ∀ axial : ℝ,
        (originalPhysicalClosedJet parameters vector).value (point,(axial : CellCircle)) =
          startupRawMatrix (originalInverseTransposeFamily parameters length epsilon baseField) raw (axial,point.val)) →
      ∀ grade,originalGradeNorm grade vector ≤ constants grade *
        (originalGradeNorm grade covariant +
          (1+physicalBudget parameters baseField rho epsilon (4+grade))*originalGradeNorm 0 covariant) := by
  obtain ⟨constants,nonnegative,solve⟩ := actualOriginalInverseTranspose_core_tame parameters length
  refine ⟨constants,nonnegative,?_⟩
  intro baseField rho epsilon small covariant vector raw regular inputSame outputSame
  obtain ⟨chosen,chosenSame,bound⟩ := solve baseField rho epsilon small covariant
  have physical := originalCore_matrixField_fidelity parameters
    (originalInverseTransposeFamily parameters length epsilon baseField)
    (originalInverseTransposeFamily_coherent parameters length rho epsilon baseField small)
    covariant vector raw regular inputSame outputSame
  have equal : chosen = vector := originalSourceFieldLinear_injective parameters
    (chosenSame.trans physical.symm)
  exact equal ▸ bound

end Grad.ActualPhysicalField
