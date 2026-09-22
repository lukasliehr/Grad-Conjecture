import AKDH3ActualRadiusAndScalarFactors

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.GaugeCoefficients.Physical.Allocation

def retainedForceRawScalar (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) (raw : ℕ) (point : ℝ) (component : Fin 3) :=
  polarEntryScalar parameters (forceMatrixFamily parameters L state.val.epsilon state.val.field)
    (forceMatrixFamily_coherent parameters L state.val.rho state.val.epsilon state.val.field state.val.low)
    0 component raw point

theorem retainedForceRawScalar_bound (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) (raw : ℕ) (radius : RadialPoint)
    (component : Fin 3) (moment : ℕ) :
    (∑' shift, productMoment parameters moment radius.val (retainedForceRawScalar parameters L compact state raw radius.val component) shift) ≤
      physicalPolarEntryConstant (forceMatrixProfile parameters L).deviation 0 component moment raw *
        physicalBudget parameters state.val.field state.val.rho state.val.epsilon (moment+raw+6) := by
  have high := forceMatrixFamily_bound parameters L state.val.rho state.val.epsilon state.val.field state.val.low (moment+raw+1)
  rw [show 5+(moment+raw+1) = moment+raw+6 by omega] at high
  have absolute := mul_le_mul_of_nonneg_right (le_abs_self ((forceMatrixProfile parameters L).deviation (moment+raw+1)))
    (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon (moment+raw+6))
  apply (polarEntryScalarMoment_bound parameters _ _ 0 component moment raw radius.val radius.property.1 radius.property.2).trans
  exact (mul_le_mul_of_nonneg_left (high.trans absolute) (polarEntryConstant_pos 0 component moment raw).le).trans_eq (mul_assoc _ _ _).symm

def actualRetainedForceBaseEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :
    ActualEulerFamily parameters L compact
      (fun state radius => radialRetainedForceDeviationKernel parameters L compact state.val radius) :=
  rowPrimitiveEulerFamily parameters L compact (retainedForceRawScalar parameters L compact)
    (fun state raw point component shift => polarEntryScalar_hasDerivAt parameters _ _ 0 component raw point shift)
    (fun state raw radius component moment => polarEntryScalarMoment_summable parameters _ _ 0 component moment raw radius.val radius.property.1 radius.property.2)
    6 (by omega) (fun component raw moment => physicalPolarEntryConstant (forceMatrixProfile parameters L).deviation 0 component moment raw)
    (fun _ _ _ => physicalPolarEntryConstant_nonnegative _ _ _ _ _)
    (retainedForceRawScalar_bound parameters L compact)

/-- Literal original AD10 retained row, including its +2e_theta part. -/
def actualRetainedForceEulerFamily (parameters : PhaseParameters) (L compact : ℝ) :
    ActualEulerFamily parameters L compact
      (fun state radius => radialRetainedForceKernel parameters L compact state.val radius) :=
  ((actualRetainedForceBaseEulerFamily parameters L compact).smul 2).add
    (ActualEulerFamily.fixed parameters L compact (fun phase => fullKernelSmul 2 (coordinateProjectionKernel phase 3 1))
      (fun p q => (sameConstantMatrixKernel p q _ _ _).smul 2))

end Grad.OriginalCartesianTameEstimate
