import AHQ8ActualGaugeInverseContinuity
import AHP10ActualRadialFirstInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.AnnularKernelContinuity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.SourceCollarCoefficients Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact)

theorem radialRotatedForceKernel_regular (kind : Fin 2) (radial : ℕ) :
    RegularKernelFamily (fun r : RadialPoint => radialRotatedForceKernel parameters L compact state r kind radial) := by
  refine regularKernelFamily_of_bound _ ?_ _
    (fun moment r => radialRotatedForceKernel_moment_le parameters L compact state r kind radial moment)
  intro shift input
  refine rowMultiplicationEntry_continuous (X := RadialPoint) 3
    (fun r component mode => angularCoefficientSequence
      (forceScalar parameters L state.data.rho state.data.epsilon state.data.field kind state.low component radial r.val) mode) ?_ shift input
  intro component mode
  exact continuous_const.mul ((forceScalar_continuous parameters L state.data.rho state.data.epsilon state.data.field kind state.low component radial mode).comp continuous_subtype_val)

theorem radialEncodedPerturbationKernel_regular
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤ radialGaugeLowRadius parameters L compact) :
    RegularKernelFamily (fun r : RadialPoint => radialEncodedPerturbationKernel parameters L compact state r small) := by
  have j := fixedRadialKernel_regular parameters encodedJKernel sameEncodedJKernel
  have rotation := fixedRadialKernel_regular parameters encodedRotationKernel sameEncodedRotationKernel
  have i0 := fixedRadialKernel_regular parameters firstCoordinateInjectionKernel (fun p q => sameConstantMatrixKernel p q _ _ _)
  have i1 := fixedRadialKernel_regular parameters secondCoordinateInjectionKernel (fun p q => sameConstantMatrixKernel p q _ _ _)
  have i2 := fixedRadialKernel_regular parameters thirdCoordinateInjectionKernel (fun p q => sameConstantMatrixKernel p q _ _ _)
  have mean := fixedRadialKernel_regular parameters (fun p => angularMeanKernel p 1) (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  have free := fixedRadialKernel_regular parameters (fun p => angularMeanFreeKernel p 1) (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  have qj := (radialGaugeQKernel_regular parameters L compact state small).comp j
  have f0 := radialForceKernel_regular parameters L compact state 0 0
  have f2 := radialForceKernel_regular parameters L compact state 1 0
  have rf0 := radialRotatedForceKernel_regular parameters L compact state 0 0
  exact (i0.comp (mean.comp (f0.comp qj))).add
    ((i1.comp (free.comp ((rf0.comp qj).add (f0.comp rotation)))).add
      (i2.comp (free.comp (f2.comp qj))))

theorem radialPreconditionedEncodedKernel_regular
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤ radialGaugeLowRadius parameters L compact) :
    RegularKernelFamily (fun r : RadialPoint => radialPreconditionedEncodedKernel parameters L compact state r small) :=
  (fixedRadialKernel_regular parameters encodedD0InverseKernel (fun p q => sameConstantMatrixKernel p q _ _ _)).comp
    (radialEncodedPerturbationKernel_regular parameters L compact state small)

/-- The exact radius-dependent first-system inverse has continuous entries
and every radius-uniform kernel moment on its original B7 low ball. -/
theorem radialEncodedFirstInverseKernel_regular
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤ radialFirstLowRadius parameters L compact) :
    RegularKernelFamily (fun r : RadialPoint => radialEncodedFirstInverseKernel parameters L compact state r small) := by
  have inverse := (radialPreconditionedEncodedKernel_regular parameters L compact state (small.trans (min_le_left _ _))).neg.negativeInverse
    (identityRadialKernel_regular parameters 3) (1 / 2) (by norm_num) (by norm_num)
    (fun r => radialPreconditionedEncodedKernel_small parameters L compact state r small)
  exact inverse.neg.comp
    (fixedRadialKernel_regular parameters encodedD0InverseKernel (fun p q => sameConstantMatrixKernel p q _ _ _))

end Grad.AnnularKernelContinuity
