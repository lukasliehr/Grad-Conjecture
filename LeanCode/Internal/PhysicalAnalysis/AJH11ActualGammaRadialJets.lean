import AJH10ActualPrimitiveSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
open scoped BigOperators ContDiff
namespace Grad.AnnularRadialSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularKernelContinuity
open Grad.ActualGaugeSigmaPrimitives Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact) (order : ℕ) (r : RadialPoint)

/-- Actual radial derivatives of the existing angular-mean gauge coefficients.
The original kernel is order zero; no new inverse is constructed. -/
def gammaJetCoefficients (row column : Fin 2) (shift : ℤ × ℤ) : ℂ :=
  if shift.1 = 0 then
    radialGaugeCoefficients parameters L compact state r row column.succ order shift else 0

theorem gammaJetCoefficients_moment_le (row column : Fin 2) (moment : ℕ)
    (shift : ℤ × ℤ) :
    productMoment parameters moment r.val
      (gammaJetCoefficients parameters L compact state order r row column) shift ≤
    productMoment parameters moment r.val
      (radialGaugeCoefficients parameters L compact state r row column.succ order) shift := by
  by_cases zero : shift.1 = 0
  · simp only [productMoment, gammaJetCoefficients, if_pos zero, le_refl]
  · simp only [productMoment, gammaJetCoefficients, if_neg zero, norm_zero, mul_zero]
    exact productMoment_nonnegative parameters moment r.val _ shift

theorem gammaJetCoefficients_moments (row column : Fin 2) (moment : ℕ) :
    Summable (productMoment parameters moment r.val
      (gammaJetCoefficients parameters L compact state order r row column)) :=
  Summable.of_nonneg_of_le (productMoment_nonnegative _ _ _ _)
    (gammaJetCoefficients_moment_le parameters L compact state order r row column moment)
    (radialGaugeCoefficients_moments parameters L compact state r row column.succ order moment)

def gammaJetKernel : RadialKernel parameters r 2 2 :=
  radialMatrixKernel parameters r 2 2
    (gammaJetCoefficients parameters L compact state order r)
    (gammaJetCoefficients_moments parameters L compact state order r)

def gammaJetMomentConstant (moment : ℕ) : ℝ :=
  Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
    ∑ row : Fin 2, ∑ column : Fin 2,
      gaugeScalarConstant parameters L compact row column.succ moment order

theorem gammaJetMomentConstant_nonnegative (moment : ℕ) :
    0 ≤ gammaJetMomentConstant parameters L compact order moment := by
  exact mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun row _ =>
    Finset.sum_nonneg fun column _ => gaugeScalarConstant_nonnegative _ _ _ _ _ _ _)

theorem gammaJetKernel_moment_le (moment : ℕ) :
    fullKernelMoment (radialKernelParameters parameters r) moment
      (gammaJetKernel parameters L compact state order r) ≤
        gammaJetMomentConstant parameters L compact order moment *
          physicalBudget parameters state.data.field state.data.rho state.data.epsilon
            (moment + order + 5) := by
  apply (radialMatrixKernel_moment_le parameters r 2 2 moment _ _).trans
  have each (row column : Fin 2) :
      (∑' shift, productMoment parameters moment r.val
        (gammaJetCoefficients parameters L compact state order r row column) shift) ≤
      gaugeScalarConstant parameters L compact row column.succ moment order *
        physicalBudget parameters state.data.field state.data.rho state.data.epsilon (moment + order + 5) :=
    ((gammaJetCoefficients_moments parameters L compact state order r row column moment).tsum_le_tsum
      (gammaJetCoefficients_moment_le parameters L compact state order r row column moment)
      (radialGaugeCoefficients_moments parameters L compact state r row column.succ order moment)).trans
      (radialGaugeCoefficients_bound parameters L compact state r row column.succ order moment)
  have summed := Finset.sum_le_sum (s := Finset.univ) fun row _ =>
    Finset.sum_le_sum (s := Finset.univ) fun column _ => each row column
  apply (mul_le_mul_of_nonneg_left summed (Real.exp_pos _).le).trans_eq
  unfold gammaJetMomentConstant
  simp only [← Finset.sum_mul]
  ring


theorem gammaJetKernel_regular :
    RegularKernelFamily (fun r : RadialPoint => gammaJetKernel parameters L compact state order r) := by
  refine regularKernelFamily_of_bound _ ?_ _
    (fun moment r => gammaJetKernel_moment_le parameters L compact state order r moment)
  intro shift input
  refine matrixMultiplicationEntry_continuous (X := RadialPoint) 2 2
    (fun r row column mode => gammaJetCoefficients parameters L compact state order r row column mode) ?_ shift input
  intro row column mode
  change Continuous (fun r : RadialPoint => if mode.1 = 0 then
    radialGaugeCoefficients parameters L compact state r row column.succ order mode else 0)
  split_ifs
  · exact radialGaugeCoefficients_continuous parameters L compact state row column.succ order mode
  · exact continuous_const

theorem radialGammaDeviationKernel_smooth (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    SmoothPolynomialFamily (source := 2) (target := 2) parameters lower positive bounded.le
      (fun radius => radialGammaDeviationKernel parameters L compact state radius) := by
  change SmoothPolynomialFamily parameters lower positive bounded.le (gammaJetKernel parameters L compact state 0)
  apply smoothPolynomialFamily_matrixJets parameters lower positive bounded
    (gammaJetKernel parameters L compact state)
    (fun order radius shift => matrixMultiplicationEntry 2 2
      (fun row column mode => if mode.1 = 0 then gaugeScalar parameters L state.data.rho state.data.alpha state.data.delta
        state.data.parameter state.data.epsilon state.data.field state.low row column.succ order radius mode else 0) shift (0,0))
    (fun _ _ _ _ => rfl) _ (gammaJetKernel_regular parameters L compact state) 0
  intro order shift radius
  exact matrixMultiplicationEntry_hasDerivAt 2 2
    (fun row column point mode => if mode.1 = 0 then gaugeScalar parameters L state.data.rho state.data.alpha state.data.delta
      state.data.parameter state.data.epsilon state.data.field state.low row column.succ order point mode else 0)
    (fun row column point mode => if mode.1 = 0 then gaugeScalar parameters L state.data.rho state.data.alpha state.data.delta
      state.data.parameter state.data.epsilon state.data.field state.low row column.succ (order + 1) point mode else 0)
    (fun row column point mode => by
      by_cases zero : mode.1 = 0
      · simp only [if_pos zero]
        exact gaugeScalar_hasDerivAt parameters L state.data.rho state.data.alpha state.data.delta
          state.data.parameter state.data.epsilon state.data.field state.low row column.succ order point mode
      · simp only [if_neg zero]
        exact hasDerivAt_const point 0) radius shift (0,0)

end Grad.AnnularRadialSmoothness
