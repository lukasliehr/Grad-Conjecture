import AHP5FixedKernelRadialBounds

noncomputable section
set_option maxHeartbeats 1400000
open scoped BigOperators

namespace Grad.AnnularReconstruction
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.SourceCollarCoefficients Grad.PhaseAlgebra
open Grad.ActualGaugeSigmaPrimitives Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)

def radialGammaCoefficients (row column : Fin 2) (shift : ℤ × ℤ) : ℂ :=
  if shift.1 = 0 then
    radialGaugeCoefficients parameters L compact state r row column.succ 0 shift else 0

theorem radialGammaCoefficients_moment_le (row column : Fin 2) (moment : ℕ)
    (shift : ℤ × ℤ) :
    productMoment parameters moment r.val
      (radialGammaCoefficients parameters L compact state r row column) shift ≤
    productMoment parameters moment r.val
      (radialGaugeCoefficients parameters L compact state r row column.succ 0) shift := by
  by_cases zero : shift.1 = 0
  · simp only [productMoment, radialGammaCoefficients, if_pos zero, le_refl]
  · simp only [productMoment, radialGammaCoefficients, if_neg zero, norm_zero, mul_zero]
    exact productMoment_nonnegative parameters moment r.val _ shift

theorem radialGammaCoefficients_moments (row column : Fin 2) (moment : ℕ) :
    Summable (productMoment parameters moment r.val
      (radialGammaCoefficients parameters L compact state r row column)) :=
  Summable.of_nonneg_of_le (productMoment_nonnegative _ _ _ _)
    (radialGammaCoefficients_moment_le parameters L compact state r row column moment)
    (radialGaugeCoefficients_moments parameters L compact state r row column.succ 0 moment)

def radialGammaDeviationKernel : RadialKernel parameters r 2 2 :=
  radialMatrixKernel parameters r 2 2
    (radialGammaCoefficients parameters L compact state r)
    (radialGammaCoefficients_moments parameters L compact state r)

def radialGammaMomentConstant (moment : ℕ) : ℝ :=
  Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
    ∑ row : Fin 2, ∑ column : Fin 2,
      gaugeScalarConstant parameters L compact row column.succ moment 0

theorem radialGammaMomentConstant_nonnegative (moment : ℕ) :
    0 ≤ radialGammaMomentConstant parameters L compact moment := by
  exact mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun row _ =>
    Finset.sum_nonneg fun column _ => gaugeScalarConstant_nonnegative _ _ _ _ _ _ _)

theorem radialGammaDeviationKernel_moment_le (moment : ℕ) :
    fullKernelMoment (radialKernelParameters parameters r) moment
      (radialGammaDeviationKernel parameters L compact state r) ≤
        radialGammaMomentConstant parameters L compact moment *
          physicalBudget parameters state.data.field state.data.rho state.data.epsilon
            (moment + 5) := by
  apply (radialMatrixKernel_moment_le parameters r 2 2 moment _ _).trans
  have each (row column : Fin 2) :
      (∑' shift, productMoment parameters moment r.val
        (radialGammaCoefficients parameters L compact state r row column) shift) ≤
      gaugeScalarConstant parameters L compact row column.succ moment 0 *
        physicalBudget parameters state.data.field state.data.rho state.data.epsilon (moment + 5) :=
    ((radialGammaCoefficients_moments parameters L compact state r row column moment).tsum_le_tsum
      (radialGammaCoefficients_moment_le parameters L compact state r row column moment)
      (radialGaugeCoefficients_moments parameters L compact state r row column.succ 0 moment)).trans
      (radialGaugeCoefficients_bound parameters L compact state r row column.succ 0 moment)
  have summed := Finset.sum_le_sum (s := Finset.univ) fun row _ =>
    Finset.sum_le_sum (s := Finset.univ) fun column _ => each row column
  apply (mul_le_mul_of_nonneg_left summed (Real.exp_pos _).le).trans_eq
  unfold radialGammaMomentConstant
  simp only [← Finset.sum_mul]
  ring

/-- One physical ball is fixed before the entire radius interval and before
all moment grades. It retains the already accepted outer-circle ball. -/
def radialGaugeLowRadius : ℝ :=
  min (actualMassInverseLowRadius parameters L compact)
    (2 * (radialGammaMomentConstant parameters L compact 0 + 1))⁻¹

theorem radialGaugeLowRadius_positive : 0 < radialGaugeLowRadius parameters L compact := by
  apply lt_min (actualMassInverseLowRadius_positive parameters L compact)
  apply inv_pos.mpr
  have := radialGammaMomentConstant_nonnegative parameters L compact 0
  linarith

private theorem smallCoefficientHalf (C budget norm : ℝ) (C0 : 0 ≤ C)
    (bound : norm ≤ C * budget) (small : budget ≤ (2 * (C + 1))⁻¹) : norm ≤ 1 / 2 := by
  apply (bound.trans (mul_le_mul_of_nonneg_left small C0)).trans
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (by linarith : 0 < 2 * (C + 1))).mpr
  nlinarith

theorem radialGammaDeviationKernel_small
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
      radialGaugeLowRadius parameters L compact) :
    fullKernelMoment (radialKernelParameters parameters r) 0
      (fullKernelNeg (radialGammaDeviationKernel parameters L compact state r)) ≤ 1 / 2 := by
  apply (fullKernelNeg_moment_le _ 0 _).trans
  apply smallCoefficientHalf
    (radialGammaMomentConstant parameters L compact 0)
    (physicalBudget parameters state.data.field state.data.rho state.data.epsilon 5)
    _ (radialGammaMomentConstant_nonnegative parameters L compact 0)
    (radialGammaDeviationKernel_moment_le parameters L compact state r 0)
  exact (physicalBudget_monotone parameters state.data.field state.data.rho state.data.epsilon
    (by omega : 5 ≤ 7)).trans (small.trans (min_le_right _ _))

def radialNegativeGammaInverseKernel
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
      radialGaugeLowRadius parameters L compact) : RadialKernel parameters r 2 2 :=
  fullKernelNegativeIdentityInverse (radialKernelParameters parameters r)
    (fullKernelNeg (radialGammaDeviationKernel parameters L compact state r)) (1 / 2)
    (radialGammaDeviationKernel_small parameters L compact state r small) (by norm_num)

def radialGaugeMeanRowsKernel : RadialKernel parameters r 3 2 :=
  fullKernelComposition (angularMeanKernel (radialKernelParameters parameters r) 2)
    (radialGaugeRowsKernel parameters L compact state r 0)

def radialGaugeCorrectionKernel
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
      radialGaugeLowRadius parameters L compact) : RadialKernel parameters r 3 3 :=
  fullKernelComposition (tailInjectionKernel (radialKernelParameters parameters r))
    (fullKernelComposition (radialNegativeGammaInverseKernel parameters L compact state r small)
      (radialGaugeMeanRowsKernel parameters L compact state r))

def radialGaugeQKernel
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
      radialGaugeLowRadius parameters L compact) : RadialKernel parameters r 3 3 :=
  fullKernelAdd (fullIdentityKernel (radialKernelParameters parameters r) 3)
    (radialGaugeCorrectionKernel parameters L compact state r small)

theorem radialNegativeGammaInverseKernel_twoSided
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
      radialGaugeLowRadius parameters L compact) :
    let negativeGamma := fullKernelNegativeIdentityPerturbation (radialKernelParameters parameters r)
      (fullKernelNeg (radialGammaDeviationKernel parameters L compact state r))
    let inverse := radialNegativeGammaInverseKernel parameters L compact state r small
    fullKernelComposition negativeGamma inverse =
      fullIdentityKernel (radialKernelParameters parameters r) 2 ∧
    fullKernelComposition inverse negativeGamma =
      fullIdentityKernel (radialKernelParameters parameters r) 2 := by
  exact ⟨fullKernelNegativeIdentity_inverse_right _ _ _ _ _,
    fullKernelNegativeIdentity_inverse_left _ _ _ _ _⟩

end Grad.AnnularReconstruction
