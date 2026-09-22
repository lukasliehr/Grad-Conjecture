import AKBC34ActualHomogeneousNegativeFirst

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.OriginalKernelRetainedDecay
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.AxisSplit Grad.BoundaryTrace
open Grad.SourceCollarFullSource Grad.AnnularSmoothCore

theorem originalCoreCircleTrace_smul {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (radius : RadialPoint) (scalar : ℂ) :
    originalCoreCircleTrace parameters (scalar • field) radius=scalar • originalCoreCircleTrace parameters field radius := by
  have represented := (originalCoreCircleTrace_represents parameters field radius).smul scalar
  have same : (fun angles => scalar • originalCoreCircle parameters field radius angles)=
      originalCoreCircle parameters (scalar • field) radius :=
    funext (fun angles => (coreValue_smul scalar field _ _).symm)
  rw [same] at represented
  exact (originalCoreCircleTrace_represents parameters _ radius).unique represented

theorem originalCoreCircleTrace_valueMap {input output : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters input) (radius : RadialPoint)
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output) :
    originalCoreCircleTrace parameters (valueMapCore parameters mapping field) radius=
      originalCircleMatrix parameters mapping (originalCoreCircleTrace parameters field radius) := by
  have represented := (originalCoreCircleTrace_represents parameters field radius).valueMap
    (originalCoreCircle_continuous parameters field radius) mapping
  have same : (fun angles => mapping (originalCoreCircle parameters field radius angles))=
      originalCoreCircle parameters (valueMapCore parameters mapping field) radius :=
    funext (fun angles => (coreValue_valueMap mapping field _ _).symm)
  rw [same] at represented
  exact (originalCoreCircleTrace_represents parameters _ radius).unique represented

theorem originalCoreCircleTrace_zero (parameters : PhaseParameters) (radius : RadialPoint) :
    originalCoreCircleTrace parameters (0 : ACore parameters 1) radius=0 := by
  apply lp.ext
  funext mode
  rw [← lambdaCircle_weighted parameters radius.val (originalCoreCircleTrace parameters 0 radius) mode,
    originalCoreCircleTrace_unweighted]
  change (_ : ℂ) • angularCoefficient (fun _ => (0 : ComplexEuclidean 1)) mode.1=0
  rw [angularCoefficient_zero,smul_zero]

theorem originalCoreCircleTrace_meanFree (parameters : PhaseParameters) (field : ACore parameters 1) (radius : RadialPoint) :
    originalCoreCircleTrace parameters (removeAngularCore parameters field) radius=
      hilbertMeanFree parameters (originalCoreCircleTrace parameters field radius) := by
  have derivative := originalCoreCircleTrace_rotation parameters (removeAngularCore parameters field) radius
  rw [rotationCore_removeAngular] at derivative
  have original := (originalCoreCircleTrace_rotation parameters field radius).meanFree (parameters := parameters)
  have mean : ∀ cell,(hilbertMeanFree parameters (originalCoreCircleTrace parameters field radius)) (0,cell)=0 := by
    intro cell
    change (if (0 : ℤ)=0 then (0 : ℂ) else 1) •
      (originalCoreCircleTrace parameters field radius) (0,cell)=(0 : ComplexEuclidean 1)
    simp
  exact (originalCircleAngularInverse_rotation parameters _ _ derivative
    (originalCoreCircleTrace_mean parameters _ (angularCore_removeAngularCore field) radius)).symm.trans
      (originalCircleAngularInverse_rotation parameters _ _ original mean)

theorem originalCoreCircleTrace_time_coefficient {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (radius : RadialPoint) (mode : ℤ×ℤ) :
    lambdaCircleCoefficient parameters radius.val (originalCoreCircleTrace parameters (timeDerivativeCore parameters field) radius) mode=
      (Complex.I*(mode.2 : ℂ)) • lambdaCircleCoefficient parameters radius.val (originalCoreCircleTrace parameters field radius) mode := by
  rw [originalCoreCircleTrace_unweighted,originalCoreCircleTrace_unweighted]
  change angularCoefficient (fun angle => ((mode.2 : ℂ)*Complex.I) • (field.val mode.2).value
    (Grad.SourceCollarDivision.polarClosedPoint radius.val angle radius.property.1 radius.property.2)) mode.1=_
  exact (angularCoefficient_smul_continuous ((mode.2 : ℂ)*Complex.I)
    (fun angle => (field.val mode.2).value
      (Grad.SourceCollarDivision.polarClosedPoint radius.val angle radius.property.1 radius.property.2)) mode.1).trans
    (congrArg (fun scalar : ℂ => scalar • angularCoefficient
      (fun angle => (field.val mode.2).value
        (Grad.SourceCollarDivision.polarClosedPoint radius.val angle radius.property.1 radius.property.2)) mode.1)
      (mul_comm (mode.2 : ℂ) Complex.I))

theorem OriginalNegativeCircle.meanFree {parameters : PhaseParameters} {radius : RadialPoint}
    {negative : NegativeTrace (radialKernelParameters parameters radius) 0 0 1} {circle : CellL2 1}
    (represented : OriginalNegativeCircle parameters radius negative circle) :
    OriginalNegativeCircle parameters radius (forceMeanFreeTrace _ 0 0 negative) (hilbertMeanFree parameters circle) := by
  intro mode
  rw [forceMeanFreeTrace,angularMeanFreeKernel,scalarModeDiagonalKernel_action_coefficient,represented mode]
  change (if mode.1=0 then (0 : ℂ) else 1) • ((_ : ℂ) • circle mode)=
    (_ : ℂ) • ((if mode.1=0 then (0 : ℂ) else 1) • circle mode)
  exact smul_comm _ _ _

end Grad.OriginalKernelCovariantRecovery
