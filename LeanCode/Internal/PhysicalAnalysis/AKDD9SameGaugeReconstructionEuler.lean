import AKDD8OriginalTenGradeEulerAllocation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.SourceCollarCoefficients Grad.AnnularRadialSmoothness
open Grad.GaugeCoefficients.Physical.Allocation

attribute [local irreducible] fullKernelComposition fullKernelAdd fullKernelSmul polynomialKernelAction

def composedEulerKernel {parameters : PhaseParameters} {source middle target : ℕ}
    (outer : ℕ → (radius : RadialPoint) → RadialKernel parameters radius middle target)
    (inner : ℕ → (radius : RadialPoint) → RadialKernel parameters radius source middle)
    (rank : ℕ) (radius : RadialPoint) : RadialKernel parameters radius source target :=
  compositionEulerKernel radius (fun raw => outer raw radius) (fun raw => inner raw radius) (eulerLeibnizTerms rank)

theorem composedEulerKernel_zero {parameters : PhaseParameters} {source middle target : ℕ}
    (outer : ℕ → (radius : RadialPoint) → RadialKernel parameters radius middle target)
    (inner : ℕ → (radius : RadialPoint) → RadialKernel parameters radius source middle)
    (radius : RadialPoint) :
    composedEulerKernel outer inner 0 radius = fullKernelComposition (outer 0 radius) (inner 0 radius) :=
  compositionEulerKernel_zero radius _ _

def originalGaugeMeanEulerKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) :=
  composedEulerKernel (fixedEulerKernel parameters (fun phase => angularMeanKernel phase 2))
    (fun rank radius => actualGaugeEulerKernel parameters L compact state.val radius rank)

def originalGaugeCorrectionEulerKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) :=
  composedEulerKernel (fixedEulerKernel parameters tailInjectionKernel)
    (composedEulerKernel
      (fun rank radius => originalGammaInverseEulerKernel parameters L compact state.val state.gaugeSmall radius rank)
      (originalGaugeMeanEulerKernel parameters L compact state))

def originalGaugeQEulerKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) (rank : ℕ) (radius : RadialPoint) :
    RadialKernel parameters radius 3 3 :=
  fullKernelAdd (fixedEulerKernel parameters (fun phase => fullIdentityKernel phase 3) rank radius)
    (originalGaugeCorrectionEulerKernel parameters L compact state rank radius)

/-- Rank zero is the existing original gauge reconstruction, literally. -/
theorem originalGaugeQEulerKernel_zero (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) (radius : RadialPoint) :
    originalGaugeQEulerKernel parameters L compact state 0 radius =
      radialGaugeQKernel parameters L compact state.val radius state.gaugeSmall := by
  unfold originalGaugeQEulerKernel originalGaugeCorrectionEulerKernel originalGaugeMeanEulerKernel
  rw [composedEulerKernel_zero,composedEulerKernel_zero,composedEulerKernel_zero]
  rfl

theorem originalGaugeQEulerKernel_derivativeTower (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    KernelEulerDerivativeTower parameters lower positive bounded.le (originalGaugeQEulerKernel parameters L compact state) := by
  unfold originalGaugeQEulerKernel originalGaugeCorrectionEulerKernel originalGaugeMeanEulerKernel composedEulerKernel
  apply KernelEulerDerivativeTower.add
  · exact fixedEulerKernel_derivativeTower parameters lower positive bounded.le _ (fun _ _ => sameFullIdentityKernel _ _ _)
  · apply KernelEulerDerivativeTower.comp
    · exact fixedEulerKernel_derivativeTower parameters lower positive bounded.le _ (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)
    · apply KernelEulerDerivativeTower.comp
      · exact originalGammaInverseEulerKernel_operatorTower parameters L compact state.val state.gaugeSmall lower positive bounded
      · apply KernelEulerDerivativeTower.comp
        · exact fixedEulerKernel_derivativeTower parameters lower positive bounded.le _ (fun _ _ => sameScalarModeDiagonalKernel _ _ _ _ _ _)
        · exact actualGaugeEulerKernel_derivativeTower parameters L compact state.val lower positive bounded

theorem actualGaugeEulerKernel_originalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    OriginalEulerMoments parameters L compact
      (fun state rank radius => actualGaugeEulerKernel parameters L compact state.val radius rank) := by
  intro rank moment
  refine ⟨actualGaugeEulerMomentConstant parameters L compact moment rank,
    actualGaugeEulerMomentConstant_nonnegative parameters L compact moment rank,?_⟩
  intro state _ radius
  apply (actualGaugeEulerKernel_moment_bound parameters L compact rank moment state.val radius).trans
  apply mul_le_mul_of_nonneg_left _ (actualGaugeEulerMomentConstant_nonnegative parameters L compact moment rank)
  exact (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon (by omega : moment+rank+5 ≤ 10+(rank+moment))).trans (by linarith)

theorem originalGammaInverseEulerKernel_originalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    OriginalEulerMoments parameters L compact
      (fun state rank radius => originalGammaInverseEulerKernel parameters L compact state.val state.gaugeSmall radius rank) := by
  intro rank moment
  refine ⟨gammaInverseEulerMomentConstant parameters L compact rank moment,
    gammaInverseEulerMomentConstant_nonnegative parameters L compact rank moment,?_⟩
  intro state low radius
  have lowSeven := (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon (by omega : 7 ≤ 10)).trans low
  apply (originalGammaInverseEulerKernel_oneHigh parameters L compact state lowSeven radius rank moment).trans
  apply mul_le_mul_of_nonneg_left _ (gammaInverseEulerMomentConstant_nonnegative parameters L compact rank moment)
  exact add_le_add le_rfl (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon (by omega))

/-- Actual reconstruction, every Euler/moment rank, one high B_(10+rank+moment),
and the full original analytic width. No product of high budgets remains. -/
theorem originalGaugeQEulerKernel_originalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    OriginalEulerMoments parameters L compact (originalGaugeQEulerKernel parameters L compact) := by
  unfold originalGaugeQEulerKernel originalGaugeCorrectionEulerKernel originalGaugeMeanEulerKernel composedEulerKernel
  apply OriginalEulerMoments.add
  · exact OriginalEulerMoments.fixed parameters L compact _ (fun _ _ => sameFullIdentityKernel _ _ _)
  · apply OriginalEulerMoments.comp
    · exact OriginalEulerMoments.fixed parameters L compact _ (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)
    · apply OriginalEulerMoments.comp
      · exact originalGammaInverseEulerKernel_originalMoments parameters L compact
      · apply OriginalEulerMoments.comp
        · exact OriginalEulerMoments.fixed parameters L compact _ (fun _ _ => sameScalarModeDiagonalKernel _ _ _ _ _ _)
        · exact actualGaugeEulerKernel_originalMoments parameters L compact

end Grad.OriginalCartesianTameEstimate
