import FC2Interface

noncomputable section

open Set
open scoped ContDiff Topology

namespace Grad.CartesianState

open Grad.ClosedJets

theorem parameters_gamma_lt_one (parameters : PhaseParameters) : parameters.gamma < 1 :=
  parameters.gamma_lt_min.trans_le (min_le_left 1 parameters.sigma0)

theorem parameters_gamma_lt_sigma0 (parameters : PhaseParameters) :
    parameters.gamma < parameters.sigma0 :=
  parameters.gamma_lt_min.trans_le (min_le_right 1 parameters.sigma0)

theorem parameters_gamma_nonnegative (parameters : PhaseParameters) : 0 ≤ parameters.gamma :=
  parameters.gamma_pos.le

theorem cellFrequency_formula (cell : ℤ) :
    cellFrequency cell = Real.sqrt (1 + (cell : ℝ) ^ 2) := rfl

theorem cellFrequency_one_le (cell : ℤ) : 1 ≤ cellFrequency cell := by
  rw [cellFrequency_formula]
  have bound : (1 : ℝ) ≤ 1 + (cell : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (cell : ℝ)]
  simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt bound

theorem cellFrequency_pos (cell : ℤ) : 0 < cellFrequency cell :=
  lt_of_lt_of_le zero_lt_one (cellFrequency_one_le cell)

theorem cellFrequency_neg (cell : ℤ) : cellFrequency (-cell) = cellFrequency cell := by
  simp [cellFrequency_formula]

theorem cellPolynomialWeight_formula (cell : ℤ) :
    cellPolynomialWeight cell = 1 + |(cell : ℝ)| := rfl

theorem cellPolynomialWeight_one_le (cell : ℤ) : 1 ≤ cellPolynomialWeight cell := by
  simp [cellPolynomialWeight, abs_nonneg]

theorem cartesianPhase_formula (parameters : PhaseParameters) (cell : ℤ)
    (point : SpatialPlane) :
    cartesianPhase parameters cell point =
      parameters.sigma0 * cellFrequency cell -
        parameters.gamma *
          (Real.sqrt (1 + cellFrequency cell ^ 2 * ‖point‖ ^ 2) - 1) := by
  rw [cartesianPhase, Grad.AnalyticWeights.Calculus.physicalPhase_formula]
  simp only [Grad.AnalyticWeights.Calculus.radicand, one_pow, one_mul, cellFrequency]
  ring_nf

theorem cartesianWeight_exp (parameters : PhaseParameters) (cell : ℤ)
    (point : SpatialPlane) :
    cartesianWeight parameters cell point = Real.exp (cartesianPhase parameters cell point) :=
  Grad.AnalyticWeights.Calculus.physicalWeight_exp parameters.sigma0 parameters.gamma 1 cell point

theorem cartesianPhase_contDiff (parameters : PhaseParameters) (cell : ℤ) :
    ContDiff ℝ ∞ (cartesianPhase parameters cell) :=
  Grad.AnalyticWeights.Calculus.physicalPhase_contDiff parameters.sigma0 parameters.gamma 1 cell

theorem cartesianWeight_contDiff (parameters : PhaseParameters) (cell : ℤ) :
    ContDiff ℝ ∞ (cartesianWeight parameters cell) := by
  exact (cartesianPhase_contDiff parameters cell).exp

theorem cartesianPhase_neg (parameters : PhaseParameters) (cell : ℤ)
    (point : SpatialPlane) :
    cartesianPhase parameters (-cell) point = cartesianPhase parameters cell point := by
  rw [cartesianPhase_formula, cartesianPhase_formula, cellFrequency_neg]

theorem cartesianWeight_neg (parameters : PhaseParameters) (cell : ℤ)
    (point : SpatialPlane) :
    cartesianWeight parameters (-cell) point = cartesianWeight parameters cell point := by
  rw [cartesianWeight_exp, cartesianWeight_exp, cartesianPhase_neg]

theorem cartesianWeight_pos (parameters : PhaseParameters) (cell : ℤ)
    (point : SpatialPlane) : 0 < cartesianWeight parameters cell point := by
  rw [cartesianWeight_exp]
  exact Real.exp_pos _

theorem cartesianWeight_one_le (parameters : PhaseParameters) (cell : ℤ)
    (point : ClosedDisk) : 1 ≤ cartesianWeight parameters cell point.val := by
  have rateNonnegative :
      0 ≤ Grad.AnalyticWeights.rate parameters.sigma0 parameters.gamma ‖point.val‖ := by
    unfold Grad.AnalyticWeights.rate
    have radiusBound : ‖point.val‖ ≤ 1 := point.property
    nlinarith [parameters_gamma_lt_sigma0 parameters, parameters.gamma_pos]
  simpa [cartesianWeight, Grad.AnalyticWeights.Calculus.physicalWeight] using
    Grad.AnalyticWeights.weight_one_le parameters.sigma0 parameters.gamma ‖point.val‖ cell
      (parameters_gamma_nonnegative parameters) (norm_nonneg _) rateNonnegative

def gradeMultiIndexEquiv (grade : ℕ) :
    GradeMultiIndex grade ≃ {index : CartesianMultiIndex // cartesianOrder index ≤ grade} where
  toFun index := ⟨index.toCartesian, index.property⟩
  invFun index := by
    have bound : index.val.1 + index.val.2 ≤ grade := by
      simpa [cartesianOrder] using index.property
    refine ⟨(⟨index.val.1, ?_⟩, ⟨index.val.2, ?_⟩), index.property⟩
    · omega
    · omega
  left_inv index := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> rfl
  right_inv index := by
    apply Subtype.ext
    apply Prod.ext <;> rfl

theorem gradeMultiIndexEquiv_apply (grade : ℕ) (index : GradeMultiIndex grade) :
    (gradeMultiIndexEquiv grade index).val = index.toCartesian := rfl

theorem gradeMultiIndex_toCartesian_injective (grade : ℕ) :
    Function.Injective (@GradeMultiIndex.toCartesian grade) := by
  intro first second equality
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg Prod.fst equality
  · exact congrArg Prod.snd equality

end Grad.CartesianState
