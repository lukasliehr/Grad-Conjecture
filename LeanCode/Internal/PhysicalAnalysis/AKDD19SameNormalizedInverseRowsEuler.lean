import AKDD18SameSevenSlotKnownRowsEuler

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.BoundaryKernelAction Grad.AnnularReconstruction
open OriginalEulerAssembly

/-- The original normalized mass row is the SAME mass inverse applied to
the complete original seven-slot right-hand side. -/
def originalRecoveredMassEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :
    ActualEulerFamily parameters L compact
      (fun state radius => radialRecoveredMassKernel parameters L compact state.val radius state.property) :=
  (originalMassInverseEulerFamily parameters L compact).comp
    ((slot parameters L compact 0).sub (originalKnownJStarEulerFamily parameters L compact))

/-- Literal normalized original covariant reconstruction. -/
def originalNormalizedCovariantEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :
    ActualEulerFamily parameters L compact
      (fun state radius => radialNormalizedCovariantKernel parameters L compact state.val radius state.property) :=
  ((originalUnknownUEulerFamily parameters L compact).comp (originalRecoveredMassEulerFamily parameters L compact)).add
    (originalKnownAStarEulerFamily parameters L compact)

/-- Literal normalized original rotated-covariant reconstruction. -/
def originalNormalizedRotatedCovariantEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :
    ActualEulerFamily parameters L compact
      (fun state radius => radialNormalizedRotatedCovariantKernel parameters L compact state.val radius state.property) :=
  ((originalUnknownVEulerFamily parameters L compact).comp (originalRecoveredMassEulerFamily parameters L compact)).add
    (originalKnownRAStarEulerFamily parameters L compact)

end Grad.OriginalCartesianTameEstimate
