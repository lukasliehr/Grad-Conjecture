import BL21WeightedDensity

noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

def reverseDerivativeConstant (order : ℕ) : ℝ :=
  ((order.factorial * inverseChartBound order ^ order) ^ 2 * (order + 1 : ℝ))

theorem reverseDerivativeConstant_nonnegative (order : ℕ) : 0 ≤ reverseDerivativeConstant order := by
  unfold reverseDerivativeConstant
  positivity

def cartesianLiftDerivativeConstant (parameters : PhaseParameters) (order : ℕ) : ℝ :=
  reverseDerivativeConstant order * polarDensityEnergyConstant parameters order

theorem cartesianLiftDerivativeConstant_nonnegative (parameters : PhaseParameters) (order : ℕ) :
    0 ≤ cartesianLiftDerivativeConstant parameters order :=
  mul_nonneg (reverseDerivativeConstant_nonnegative order) (polarDensityEnergyConstant_nonnegative parameters order)

theorem weightedFiniteKernel_derivative_collar {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (modes : Finset ℤ) (values : ℤ → ComplexEuclidean dimension) (order : ℕ) :
    collarIntegral (fun point => ‖iteratedFDeriv ℝ order
      (weightedFiniteKernelField parameters cell modes values) (collarPlane point)‖ ^ 2) ≤
      reverseDerivativeConstant order * collarIntegral
        (polarJetSquaredDensity (finitePolarField parameters cell modes
          (fun mode => (Real.exp (boundaryPhase parameters cell) : ℂ) • values mode)) order) := by
  let field := weightedFiniteKernelField parameters cell modes values
  let polar := finitePolarField parameters cell modes
    (fun mode => (Real.exp (boundaryPhase parameters cell) : ℂ) • values mode)
  have smooth : ContDiff ℝ ∞ field := weightedFiniteKernelField_smooth parameters cell modes values
  have polarSmooth : ContDiff ℝ ∞ polar := finitePolarField_smooth parameters cell modes _
  have sourceContinuous : Continuous (fun point => ‖iteratedFDeriv ℝ order field (collarPlane point)‖ ^ 2) :=
    (((smooth.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).comp
      collarPlane_smooth.continuous).norm).pow 2
  have targetContinuous : Continuous (fun point => reverseDerivativeConstant order * polarJetSquaredDensity polar order point) :=
    continuous_const.mul (polarJetSquaredDensity_continuous polar polarSmooth order)
  have comparison := collarIntegral_mono _ _ sourceContinuous targetContinuous (by
    intro point inside
    have reverse := reverseCollar_derivative_sq_bound field smooth order order le_rfl point inside.1
    apply reverse.trans_eq
    congr 1
    unfold polarJetSquaredDensity
    apply Finset.sum_congr rfl
    intro index _
    rw [weightedFiniteKernelField_polar_derivative parameters cell modes values index point (by linarith [inside.1.2])])
  rw [collarIntegral_const_mul] at comparison
  exact comparison

theorem weightedFiniteKernel_cartesian_energy {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (modes : Finset ℤ) (values : ℤ → ComplexEuclidean dimension) (grade order : ℕ)
    (gradePositive : 1 ≤ grade) (orderBound : order ≤ grade) :
    cellFrequency cell ^ (2 * (grade - order)) *
      (∫ point in closedUnitDisk,
        ‖iteratedFDeriv ℝ order (weightedFiniteKernelField parameters cell modes values) point‖ ^ 2) ≤
      cartesianLiftDerivativeConstant parameters order * ∑ mode ∈ modes,
        Real.exp (2 * boundaryPhase parameters cell) * boundaryFrequency (mode, cell) ^ (2 * grade - 1) *
          ‖values mode‖ ^ 2 := by
  let field := weightedFiniteKernelField parameters cell modes values
  have smooth : ContDiff ℝ ∞ field := weightedFiniteKernelField_smooth parameters cell modes values
  have continuousDensity : Continuous (fun point => ‖iteratedFDeriv ℝ order field point‖ ^ 2) :=
    ((smooth.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).norm).pow 2
  have diskBound := disk_integral_le_collar _ continuousDensity (fun _ => sq_nonneg _) (by
    intro point inside
    rw [weightedFiniteKernelField_derivative_zero parameters cell modes values order point inside, norm_zero, zero_pow (by norm_num)])
  have collarBound := weightedFiniteKernel_derivative_collar parameters cell modes values order
  have comparison := mul_le_mul_of_nonneg_left (diskBound.trans collarBound)
    (pow_nonneg (cellFrequency_pos cell).le (2 * (grade - order)))
  have polarBound := finitePolarField_weighted_density parameters cell modes
    (fun mode => (Real.exp (boundaryPhase parameters cell) : ℂ) • values mode) grade order gradePositive orderBound
  apply comparison.trans
  calc
    _ = reverseDerivativeConstant order * (cellFrequency cell ^ (2 * (grade - order)) *
        collarIntegral (polarJetSquaredDensity (finitePolarField parameters cell modes
          (fun mode => (Real.exp (boundaryPhase parameters cell) : ℂ) • values mode)) order)) := by ring
    _ ≤ reverseDerivativeConstant order * (polarDensityEnergyConstant parameters order * ∑ mode ∈ modes,
        boundaryFrequency (mode, cell) ^ (2 * grade - 1) *
          ‖(Real.exp (boundaryPhase parameters cell) : ℂ) • values mode‖ ^ 2) :=
      mul_le_mul_of_nonneg_left polarBound (reverseDerivativeConstant_nonnegative order)
    _ = _ := by
      rw [cartesianLiftDerivativeConstant, mul_assoc]
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro mode _
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        mul_pow, show Real.exp (2 * boundaryPhase parameters cell) = Real.exp (boundaryPhase parameters cell) ^ 2 by
          rw [two_mul, Real.exp_add, pow_two]]
      ring

end Grad.BoundaryLift
