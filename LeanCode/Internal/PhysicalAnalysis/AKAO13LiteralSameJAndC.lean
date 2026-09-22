import AKAO12LiteralSameRetainedForce

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
open Grad.AnnularStrongData Grad.AnnularCoupledInverse Grad.AnnularStrongSolution

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)

/-- The exact original raw j row; the original radial equation applies P to this row. -/
theorem fullField_originalJ {row : DivisionRow 7 lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.lowPhysicalCurves parameters length compact lower positive bounded state 0).fullField bounded (radius,angles) 0 =
      (curves.rotatedCovariant parameters length compact lower positive bounded state.val).fullField bounded (radius,angles) 0 -
      ∑ component : Fin 3,originalRetainedForceRow parameters length state.val.val.epsilon state.val.val.field
        angles.2 angles.1 (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) component *
        (curves.covariant parameters length compact lower positive bounded state.val).fullField bounded (radius,angles) component := by
  rw [sameFirstPhysicalRow_pointwise parameters length compact lower positive bounded state curves radius inside angles,
    PiLp.sub_apply,fullField_originalRetainedForce parameters length compact lower positive bounded state
      (curves.covariant parameters length compact lower positive bounded state.val) radius inside angles,
    (curves.rotatedCovariant parameters length compact lower positive bounded state.val).fullField_bulkUnit bounded (0 : Fin 1) 0 radius inside angles]
  simp [matrixUnit_apply,operatorBasis]

/-- The exact original c row is the angular derivative of literal b3, with its kappa3 correction. -/
theorem fullField_originalC (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (solution : CoupledSpace lower length positive lengthPositive)
    (curves : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution))
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (polar axial : ℝ) :
    HasDerivAt (fun angle =>
      (∑ component : Fin 3,originalSignedCofactorRow parameters length state.val.val.epsilon state.val.val.field
        2 axial angle (polarClosedPoint radius angle (positive.le.trans inside.1) inside.2) component *
          (curves.covariant parameters length compact lower positive bounded state.val).fullField bounded (radius,angle,axial) component) +
      originalSignedCofactorRow parameters length state.val.val.epsilon state.val.val.field
        1 axial angle (polarClosedPoint radius angle (positive.le.trans inside.1) inside.2) 2 *
          curves.fullField bounded (radius,angle,axial) 3)
      ((curves.lowPhysicalCurves parameters length compact lower positive bounded state 1).fullField bounded (radius,polar,axial) 0) polar := by
  have derivative := ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt polar
    (sharedBThree_classical_angular parameters length compact lower positive bounded state lengthPositive data solution curves radius inside polar axial)
  change HasDerivAt (fun angle => (curves.bThree parameters length compact lower positive bounded state).fullField bounded (radius,angle,axial) 0)
    ((curves.lowPhysicalCurves parameters length compact lower positive bounded state 1).fullField bounded (radius,polar,axial) 0) polar at derivative
  have same := fun angle => fullField_originalBThree parameters length compact lower positive bounded state curves radius inside (angle,axial)
  simpa only [funext same] using derivative

end Grad.ActualPolarFlux
