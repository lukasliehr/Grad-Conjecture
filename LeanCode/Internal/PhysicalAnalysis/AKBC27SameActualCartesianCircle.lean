import AKBC26SameCovariantCircleCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra Grad.SourceCollarFullSource
open Grad.AnnularReconstruction Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.BoundaryKernelAction Grad.OriginalKernelRetainedDecay Grad.OriginalKernelGraphRestriction
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.SourceCollar Grad.ActualPhysicalField

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 6≤originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (vector : ACore parameters 3)
    (radius : Icc lower (1 : ℝ))

theorem originalCartesianCovariantCircle_represents :
    OriginalCircleRepresents parameters (tupleRadius lower positive radius)
      (originalCircleFamilyAction parameters (originalTransposeFrameFamily parameters length epsilon base)
        (originalTransposeFrameFamily_estimate parameters length rho epsilon base small).actualCoherent
        (tupleRadius lower positive radius) (originalCoreCircleTrace parameters vector (tupleRadius lower positive radius)))
      (fun angles => (originalCartesianCovariantCurves parameters length rho epsilon base small lower positive bounded vector).fullField
        bounded (radius.val,angles)) := by
  intro mode
  have represented := (originalCoreCircleTrace_represents parameters vector (tupleRadius lower positive radius)).matrix_literal
    parameters (originalTransposeFrameFamily parameters length epsilon base)
    (originalTransposeFrameFamily_estimate parameters length rho epsilon base small).actualCoherent
    (tupleRadius lower positive radius) (originalCoreCircleTrace parameters vector (tupleRadius lower positive radius))
    (originalCoreCircle parameters vector (tupleRadius lower positive radius))
    (originalCoreCircle_continuous parameters vector (tupleRadius lower positive radius)) mode
  refine represented.trans ?_
  congr 1
  funext angles
  rw [originalTransposeFrameFamily_matrix parameters length rho epsilon base small]
  exact (originalCartesianCovariantCurves_fullField parameters length rho epsilon base small lower positive bounded vector
    radius.val radius.property angles).symm

end Grad.OriginalKernelCovariantRecovery
