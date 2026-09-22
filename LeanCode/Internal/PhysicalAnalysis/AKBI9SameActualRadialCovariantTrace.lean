import AKBI8SameOriginalNegativeTraceAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.OriginalKernelRetainedDecay Grad.OriginalKernelCovariantRecovery Grad.OriginalKernelGraphRestriction
open Grad.AnnularReconstruction Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField Grad.SourceCollarFullSource
open Grad.BoundaryKernelAction Grad.ActualPolarEquations Grad.FinitePhysicalJetLift
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 6≤originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (vector : ACore parameters 3) (radius : Icc lower (1 : ℝ))

theorem originalActualRadialTrace_euler :
    (radius.val : ℂ) • forceCoordinateTrace _ 0 0 0
      (originalCurveNegativeTrace (originalPolarCovariantCurves parameters length rho epsilon base small lower positive bounded vector) radius)=
    originalCurveNegativeTrace (originalCoreLowCurves parameters lower positive bounded
      (dotOperation parameters (eulerCore parameters (planarReferenceCore parameters+base)) vector)) radius := by
  rw [← originalCurveNegativeTrace_coordinate _ bounded 0 radius]
  apply originalScalarTrace_scale _ _ bounded (radius.val : ℂ) radius
  intro angles
  rw [SmoothLowPhysicalRow.fullField_bulkUnit _ bounded (0 : Fin 1) 0 radius.val radius.property angles,
    originalPolarCovariantCurves_fullField parameters length rho epsilon base small lower positive bounded vector radius.val radius.property angles,
    originalPolarCovariantValue_radial,
    originalCoreLowCurves_fullField parameters lower positive bounded _ radius.val radius.property angles]
  exact originalRadialFrame_dot parameters length epsilon base vector (tupleRadius lower positive radius) angles

theorem originalActualRotatedRadialTrace_euler :
    (radius.val : ℂ) • forceCoordinateTrace _ 0 0 0
      (originalCurveNegativeRotation (originalPolarCovariantCurves parameters length rho epsilon base small lower positive bounded vector) radius)=
    originalCurveNegativeTrace (originalCoreLowCurves parameters lower positive bounded
      (rotationCore parameters (dotOperation parameters (eulerCore parameters (planarReferenceCore parameters+base)) vector))) radius := by
  rw [← originalCoreNegativeTrace_rotation parameters lower positive bounded _ radius]
  exact originalScaledAngularDerivative_unique
    ((originalCurveNegativeRotation_derivative _ bounded radius).constantMatrix (matrixUnit (0 : Fin 1) (0 : Fin 3)))
    (originalCurveNegativeRotation_derivative _ bounded radius) (radius.val : ℂ)
    (originalActualRadialTrace_euler parameters length rho epsilon base small lower positive bounded vector radius)

end Grad.OriginalKernelHomogeneousGraph
