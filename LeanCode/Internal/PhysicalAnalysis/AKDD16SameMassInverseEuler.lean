import AKDD15ActualUnknownMassRowsEuler
import AJH15SameFullReconstructionSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.AnnularRadialSmoothness

/-- The SAME actual scalar mass inverse, with the genuine ordered Euler
derivatives and one-high moment allocation supplied constructively. -/
def originalMassInverseEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :
    ActualEulerFamily parameters L compact
      (fun state radius => radialMassInverseKernel parameters L compact state.val radius state.property) :=
  (originalMassPerturbationEulerFamily parameters L compact).negativeInverse
    (fun state lower positive bounded => radialMassPerturbationKernel_smooth parameters L compact state lower positive bounded)
    (1/2) (by norm_num)
    (fun state radius => radialMassPerturbationKernel_small parameters L compact state.val radius state.property)
    (radialMassInverseKernel_physicalMoments parameters L compact)

end Grad.OriginalCartesianTameEstimate
