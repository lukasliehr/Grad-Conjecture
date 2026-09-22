import AHP26RadialPhysicalMomentFamilies

noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators
namespace Grad.AnnularReconstruction
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.SourceCollarCoefficients Grad.ActualGaugeSigmaPrimitives
open Grad.GaugeCoefficients.Physical.Allocation

theorem radialGaugeRowsKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun state r => radialGaugeRowsKernel parameters L compact state.val r 0) := by
  intro moment
  let constant := Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
    ∑ row : Fin 2, ∑ column : Fin 3, gaugeScalarConstant parameters L compact row column moment 0
  refine ⟨|constant|, abs_nonneg _, ?_⟩
  intro state r
  apply (radialGaugeRowsKernel_moment_le parameters L compact state.val r 0 moment).trans
  exact mul_le_mul (le_abs_self constant) (state.val.budget_le_size moment (moment + 0 + 5) (by omega))
    (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon _)
    (abs_nonneg constant)

theorem radialGammaDeviationKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun state r => radialGammaDeviationKernel parameters L compact state.val r) := by
  intro moment
  refine ⟨radialGammaMomentConstant parameters L compact moment,
    radialGammaMomentConstant_nonnegative _ _ _ _, ?_⟩
  intro state r
  exact (radialGammaDeviationKernel_moment_le parameters L compact state.val r moment).trans
    (mul_le_mul_of_nonneg_left (state.val.budget_le_size moment (moment + 5) (by omega))
      (radialGammaMomentConstant_nonnegative _ _ _ _))

theorem radialNegativeGammaInverseKernel_physicalMoments
    (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun state r => radialNegativeGammaInverseKernel parameters L compact state.val r state.gaugeSmall) := by
  unfold radialNegativeGammaInverseKernel
  apply UniformRadialKernelMoments.negativeIdentityInverse (fun state => state.val.one_le_size)
  exact (radialGammaDeviationKernel_physicalMoments parameters L compact).neg

theorem radialGaugeQKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun state r => radialGaugeQKernel parameters L compact state.val r state.gaugeSmall) := by
  unfold radialGaugeQKernel radialGaugeCorrectionKernel radialGaugeMeanRowsKernel
  apply UniformRadialKernelMoments.add
  · exact RadialPhysicalMoments.fixed parameters L compact _ (fun _ _ => sameFullIdentityKernel _ _ _)
  · apply RadialPhysicalMoments.comp
    · exact RadialPhysicalMoments.fixed parameters L compact _ (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)
    · apply RadialPhysicalMoments.comp
      · exact radialNegativeGammaInverseKernel_physicalMoments parameters L compact
      · apply RadialPhysicalMoments.comp
        · exact RadialPhysicalMoments.fixed parameters L compact _
            (fun _ _ => sameScalarModeDiagonalKernel _ _ _ _ _ _)
        · exact radialGaugeRowsKernel_physicalMoments parameters L compact

end Grad.AnnularReconstruction
