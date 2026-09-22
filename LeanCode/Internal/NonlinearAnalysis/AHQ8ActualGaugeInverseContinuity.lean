import AHQ7PhysicalCoefficientContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.AnnularKernelContinuity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.SourceCollarCoefficients Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact)

theorem radialGammaDeviationKernel_regular :
    RegularKernelFamily (fun r : RadialPoint => radialGammaDeviationKernel parameters L compact state r) := by
  refine regularKernelFamily_of_bound _ ?_ _
    (fun moment r => radialGammaDeviationKernel_moment_le parameters L compact state r moment)
  intro shift input
  refine matrixMultiplicationEntry_continuous (X := RadialPoint) 2 2
    (fun r row column mode => radialGammaCoefficients parameters L compact state r row column mode) ?_ shift input
  intro row column mode
  change Continuous (fun r : RadialPoint => if mode.1 = 0 then
    radialGaugeCoefficients parameters L compact state r row column.succ 0 mode else 0)
  split_ifs
  · exact radialGaugeCoefficients_continuous parameters L compact state row column.succ 0 mode
  · exact continuous_const

theorem radialNegativeGammaInverseKernel_regular
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤ radialGaugeLowRadius parameters L compact) :
    RegularKernelFamily (fun r : RadialPoint => radialNegativeGammaInverseKernel parameters L compact state r small) := by
  exact (radialGammaDeviationKernel_regular parameters L compact state).neg.negativeInverse
    (identityRadialKernel_regular parameters 2) (1 / 2) (by norm_num) (by norm_num)
    (fun r => radialGammaDeviationKernel_small parameters L compact state r small)

theorem radialGaugeQKernel_regular
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤ radialGaugeLowRadius parameters L compact) :
    RegularKernelFamily (fun r : RadialPoint => radialGaugeQKernel parameters L compact state r small) := by
  have tail := fixedRadialKernel_regular parameters tailInjectionKernel
    (fun first second => sameConstantMatrixKernel first second _ _ _)
  have mean := fixedRadialKernel_regular parameters (fun p => angularMeanKernel p 2)
    (fun first second => sameScalarModeDiagonalKernel first second 2 _ _ _)
  exact (identityRadialKernel_regular parameters 3).add
    (tail.comp ((radialNegativeGammaInverseKernel_regular parameters L compact state small).comp
      (mean.comp (radialGaugeRowsKernel_regular parameters L compact state 0))))

end Grad.AnnularKernelContinuity
