import AKAO8SamePolarCofactorComponent

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualPolarFlux
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.SourceCollar

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) (cofactorRow component : Fin 3)
    {row : DivisionRow 1 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

def _root_.Grad.ActualSmoothPhysicalField.SmoothLowPhysicalRow.signedCofactorComponent :
    SmoothLowPhysicalRow parameters lower positive
      (regularRadialBulkAction parameters 0 lower positive bounded.le
        (radialSignedCofactorComponentKernel parameters length compact state cofactorRow component)
        (radialSignedCofactorComponentKernel_regular parameters length compact state cofactorRow component) row) :=
  curves.action parameters lower positive bounded _
    (radialSignedCofactorComponentKernel_regular parameters length compact state cofactorRow component)
    (actualSignedCofactorComponent_conjugated_smooth parameters length compact state lower positive bounded cofactorRow component)

/-- The actual off-diagonal scalar cofactor action is literal multiplication on the SAME field. -/
theorem fullField_signedCofactorComponent_offDiagonal (different : cofactorRow ≠ component)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.signedCofactorComponent parameters length compact lower positive bounded state cofactorRow component).fullField bounded (radius,angles) =
      originalSignedCofactorRow parameters length state.val.val.epsilon state.val.val.field
        cofactorRow angles.2 angles.1 (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) component •
          curves.fullField bounded (radius,angles) := by
  have same := fullField_action_congr parameters lower positive bounded curves
    (radialSignedCofactorComponentKernel parameters length compact state cofactorRow component)
    (radialCofactorJetComponentKernel parameters length compact state cofactorRow component 0 0)
    (radialSignedCofactorComponentKernel_regular parameters length compact state cofactorRow component)
    (radialCofactorJetComponentKernel_regular parameters length compact state cofactorRow component 0 0)
    (actualSignedCofactorComponent_conjugated_smooth parameters length compact state lower positive bounded cofactorRow component)
    (actualCofactorComponent_conjugated_smooth parameters length compact state lower positive bounded cofactorRow component 0 0)
    (fun r => by
      apply FullTwoFrequencyKernel.ext_entry
      intro shift mode
      simp [radialSignedCofactorComponentKernel,circularCofactorComponentKernel,different]) radius inside angles
  change (curves.signedCofactorComponent parameters length compact lower positive bounded state cofactorRow component).fullField bounded (radius,angles) =
    (curves.cofactorDeviationComponent parameters length compact lower positive bounded state cofactorRow component).fullField bounded (radius,angles) at same
  rw [same,fullField_cofactorDeviationComponentProduct parameters length compact lower positive bounded state cofactorRow component curves radius inside angles]
  simp [polarFamilyAngleEntry,
    originalCofactorDeviation_matrix parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low,
    polarMatrixEntry_add,polarMatrixEntry_one,originalSignedCofactorRow,different]

end Grad.ActualPolarFlux
