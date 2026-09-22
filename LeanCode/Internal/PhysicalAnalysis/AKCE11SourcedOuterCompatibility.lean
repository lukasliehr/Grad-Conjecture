import AKCE3FullSourcedOuterSeven

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives
open Grad.AnnularForwardTraces Grad.AnnularPhysicalSolution Grad.AnnularStrongData Grad.AnnularSourceGraph
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularCrossMaps Grad.AnnularCurrentBoundary
open Grad.AnnularCurrentSource Grad.AnnularStrongOrbit Grad.OriginalKernelOuterUniqueness Grad.AnnularSmoothCore

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0<lower)
    (lowerHalf : lower≤1/2) (lengthPositive : 0<length)
    (candidate : CoupledSpace lower length positive lengthPositive)
    (graphs : HighKnownGraphHilbert parameters lower)

 theorem originalFullOuterSeven_supported :
    IsAngularMeanFree parameters 0 0
      (originalFullOuterSeven parameters length lower positive lowerHalf lengthPositive candidate graphs 0) := by
  intro cell
  rw [originalFullOuterSeven_sourcedCoefficient]
  change negativeTraceCoefficient parameters 0 0 (originalOuterX parameters lower length positive lowerHalf lengthPositive candidate) (0,cell)=0
  rw [originalOuterX_physical]
  exact sameCoupledXCoefficient_meanZero parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive candidate 0 _ cell

 theorem originalFullOuterSeven_scalarDerivative :
    IsAngularDerivative parameters 0 0
      (originalFullOuterSeven parameters length lower positive lowerHalf lengthPositive candidate graphs 3)
      (originalFullOuterSeven parameters length lower positive lowerHalf lengthPositive candidate graphs 1) := by
  intro mode
  rw [originalFullOuterSeven_sourcedCoefficient,originalFullOuterSeven_sourcedCoefficient]
  rfl

end Grad.OriginalCoreRealization
