import AKDH12SamePhysicalEulerAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularGeneralSourceRegularity Grad.GaugeCoefficients.Physical.Allocation

/-- The literal three kappa factors appearing in AKV28's actual G3 source.
Their Euler derivatives stay with the ordered coefficient word, so the
terminal source remains the original state-independent Cartesian input. -/
def actualSourceKappaEulerFamily (parameters : PhaseParameters) (L compact : ℝ) (component : Fin 3) :
    ActualEulerFamily parameters L compact
      (fun state radius => actualSourceKappaKernel parameters L state.val.rho state.val.epsilon
        state.val.field state.val.low component radius) :=
  scalarPrimitiveEulerFamily parameters L compact
    (fun state raw radius => kappaScalar parameters L state.val.rho state.val.epsilon state.val.field state.val.low component raw radius)
    (fun state raw point shift => kappaScalar_hasDerivAt parameters L state.val.rho state.val.epsilon state.val.field state.val.low component shift raw point)
    (fun state raw radius moment => kappaScalarMoment_summable parameters L state.val.rho state.val.epsilon state.val.field state.val.low component moment raw radius.val radius.property.1 radius.property.2)
    5 (by omega) (fun raw moment => kappaFourierConstant parameters L moment raw)
    (fun raw moment => (kappaFourierConstant_pos parameters L moment raw).le)
    (fun state raw radius moment => kappaScalarMoment_bound parameters L state.val.rho state.val.epsilon state.val.field state.val.low component moment raw radius.val radius.property.1 radius.property.2)

end Grad.OriginalCartesianTameEstimate
