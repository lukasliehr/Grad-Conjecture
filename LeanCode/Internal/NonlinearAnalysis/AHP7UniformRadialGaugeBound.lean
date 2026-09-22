import AHP6ActualRadialGaugeInverse

noncomputable section
set_option maxHeartbeats 1400000
open scoped BigOperators

namespace Grad.AnnularReconstruction
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.SourceCollarCoefficients Grad.PhaseAlgebra
open Grad.ActualGaugeSigmaPrimitives Grad.GaugeCoefficients.Physical.Allocation

theorem sameFullIdentityKernel (first second : PhaseParameters) (dimension : ℕ) :
    SameKernelEntries (fullIdentityKernel first dimension) (fullIdentityKernel second dimension) := by
  intro shift mode
  rfl

def uniformFixedMoment (parameters : PhaseParameters) {input output : ℕ}
    (family : (p : PhaseParameters) → FullTwoFrequencyKernel p input output) : ℝ :=
  fullKernelMoment (maximalKernelParameters parameters) 0
    (family (maximalKernelParameters parameters))

theorem uniformFixedMoment_nonnegative (parameters : PhaseParameters) {input output : ℕ}
    (family : (p : PhaseParameters) → FullTwoFrequencyKernel p input output) :
    0 ≤ uniformFixedMoment parameters family := fullKernelMoment_nonnegative _ _ _

theorem uniformFixedMoment_bound (parameters : PhaseParameters) (r : RadialPoint)
    {input output : ℕ} (family : (p : PhaseParameters) → FullTwoFrequencyKernel p input output)
    (same : ∀ first second, SameKernelEntries (family first) (family second)) :
    fullKernelMoment (radialKernelParameters parameters r) 0
      (family (radialKernelParameters parameters r)) ≤ uniformFixedMoment parameters family :=
  (same _ _).radialMoment_le parameters r 0

def radialNeumannBaseConstant (parameters : PhaseParameters) (dimension : ℕ) : ℝ :=
  uniformFixedMoment parameters (fun p => fullIdentityKernel p dimension) +
    fullKernelNeumannConstant 0 (1 / 2) * (1 / 2)

theorem radialNeumannBaseConstant_nonnegative (parameters : PhaseParameters) (dimension : ℕ) :
    0 ≤ radialNeumannBaseConstant parameters dimension := by
  unfold radialNeumannBaseConstant fullKernelNeumannConstant
  exact add_nonneg (uniformFixedMoment_nonnegative _ _)
    (mul_nonneg (tsum_nonneg fun _ => by positivity) (by norm_num))

theorem radialNegativeGammaInverseKernel_bound
    (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
      radialGaugeLowRadius parameters L compact) :
    fullKernelMoment (radialKernelParameters parameters r) 0
      (radialNegativeGammaInverseKernel parameters L compact state r small) ≤
        radialNeumannBaseConstant parameters 2 := by
  apply (fullKernelNegativeIdentityInverse_moment_le _ _ _ _ _ _).trans
  apply add_le_add
  · exact uniformFixedMoment_bound parameters r _ (fun first second => sameFullIdentityKernel first second 2)
  · exact mul_le_mul_of_nonneg_left
      (radialGammaDeviationKernel_small parameters L compact state r small)
      (by unfold fullKernelNeumannConstant; exact tsum_nonneg fun _ => by positivity)

def radialGaugeRowsBaseConstant (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
    ∑ kind : Fin 2, ∑ component : Fin 3, gaugeScalarConstant parameters L compact kind component 0 0

theorem radialGaugeRowsBaseConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) :
    0 ≤ radialGaugeRowsBaseConstant parameters L compact := by
  exact mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => gaugeScalarConstant_nonnegative _ _ _ _ _ _ _)

def radialGaugeQBaseConstant (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  uniformFixedMoment parameters (fun p => fullIdentityKernel p 3) +
    uniformFixedMoment parameters tailInjectionKernel *
      (radialNeumannBaseConstant parameters 2 *
        (uniformFixedMoment parameters (fun p => angularMeanKernel p 2) *
          radialGaugeRowsBaseConstant parameters L compact))

theorem radialGaugeQBaseConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) :
    0 ≤ radialGaugeQBaseConstant parameters L compact := by
  unfold radialGaugeQBaseConstant
  exact add_nonneg (uniformFixedMoment_nonnegative _ _)
    (mul_nonneg (uniformFixedMoment_nonnegative _ _)
      (mul_nonneg (radialNeumannBaseConstant_nonnegative _ _)
        (mul_nonneg (uniformFixedMoment_nonnegative _ _)
          (radialGaugeRowsBaseConstant_nonnegative _ _ _))))

theorem radialGaugeQKernel_bound (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
      radialGaugeLowRadius parameters L compact) :
    fullKernelMoment (radialKernelParameters parameters r) 0
      (radialGaugeQKernel parameters L compact state r small) ≤
        radialGaugeQBaseConstant parameters L compact := by
  have budgetFive : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 5 ≤ 1 :=
    (physicalBudget_monotone parameters state.data.field state.data.rho state.data.epsilon
      (by omega : 5 ≤ 6)).trans (state.low.trans (min_le_left _ _))
  have rows := (radialGaugeRowsKernel_moment_le parameters L compact state r 0 0).trans
    ((mul_le_mul_of_nonneg_left budgetFive
      (radialGaugeRowsBaseConstant_nonnegative parameters L compact)).trans_eq (mul_one _))
  have mean := uniformFixedMoment_bound parameters r (fun p => angularMeanKernel p 2)
    (fun first second => sameScalarModeDiagonalKernel first second 2 _ _ _)
  have tail := uniformFixedMoment_bound parameters r tailInjectionKernel
    (fun first second => sameConstantMatrixKernel first second _ _ _)
  have identity := uniformFixedMoment_bound parameters r (fun p => fullIdentityKernel p 3)
    (fun first second => sameFullIdentityKernel first second 3)
  have meanRows := fullKernelComposition_zero_moment_le_of _ _ _ _ mean rows
    (uniformFixedMoment_nonnegative _ _) (radialGaugeRowsBaseConstant_nonnegative _ _ _)
  have inverse := radialNegativeGammaInverseKernel_bound parameters L compact state r small
  have nested := fullKernelComposition_zero_moment_le_of _ _ _ _ inverse meanRows
    (radialNeumannBaseConstant_nonnegative _ _)
    ((fullKernelMoment_nonnegative _ 0 _).trans meanRows)
  have correction := fullKernelComposition_zero_moment_le_of _ _ _ _ tail nested
    (uniformFixedMoment_nonnegative _ _)
    ((fullKernelMoment_nonnegative _ 0 _).trans nested)
  exact (fullKernelAdd_moment_le _ 0 _ _).trans (add_le_add identity correction)

end Grad.AnnularReconstruction
