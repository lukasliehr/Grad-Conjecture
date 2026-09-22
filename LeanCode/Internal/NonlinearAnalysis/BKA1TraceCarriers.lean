import SBT17PublicOuterTrace

noncomputable section

open Set
open scoped BigOperators ENNReal

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace
open Grad.SourceCollarDivision Grad.SourceBoundaryTrace

/-- The literal product weight in the two tangential frequencies. -/
def splitTangentialWeight (angular cell : ℕ) (mode : ℤ × ℤ) : ℝ :=
  (1 + |(mode.1 : ℝ)|) ^ angular * (1 + |(mode.2 : ℝ)|) ^ cell

theorem splitTangentialWeight_pos (angular cell : ℕ) (mode : ℤ × ℤ) :
    0 < splitTangentialWeight angular cell mode := by
  unfold splitTangentialWeight
  positivity

/-- AH16 with the negative half power of the literal
`nu = 1 + |m| + |n|`. -/
def negativeTraceWeightSq (parameters : PhaseParameters) (angular cell : ℕ)
    (mode : ℤ × ℤ) : ℝ :=
  Real.exp (2 * boundaryPhase parameters mode.2) *
    (1 + |(mode.1 : ℝ)|) ^ (2 * angular) *
    (1 + |(mode.2 : ℝ)|) ^ (2 * cell) *
    (annularFrequency mode.1 mode.2)⁻¹

/-- AH16 with the positive half power of the same literal total frequency. -/
def positiveTraceWeightSq (parameters : PhaseParameters) (angular cell : ℕ)
    (mode : ℤ × ℤ) : ℝ :=
  Real.exp (2 * boundaryPhase parameters mode.2) *
    (1 + |(mode.1 : ℝ)|) ^ (2 * angular) *
    (1 + |(mode.2 : ℝ)|) ^ (2 * cell) *
    annularFrequency mode.1 mode.2

theorem negativeTraceWeightSq_pos (parameters : PhaseParameters) (angular cell : ℕ)
    (mode : ℤ × ℤ) : 0 < negativeTraceWeightSq parameters angular cell mode := by
  unfold negativeTraceWeightSq
  exact mul_pos
    (mul_pos
      (mul_pos (Real.exp_pos _)
        (pow_pos (by positivity : 0 < 1 + |(mode.1 : ℝ)|) _))
      (pow_pos (by positivity : 0 < 1 + |(mode.2 : ℝ)|) _))
    (inv_pos.mpr (annularFrequency_pos mode))

theorem positiveTraceWeightSq_pos (parameters : PhaseParameters) (angular cell : ℕ)
    (mode : ℤ × ℤ) : 0 < positiveTraceWeightSq parameters angular cell mode := by
  unfold positiveTraceWeightSq
  exact mul_pos
    (mul_pos
      (mul_pos (Real.exp_pos _)
        (pow_pos (by positivity : 0 < 1 + |(mode.1 : ℝ)|) _))
      (pow_pos (by positivity : 0 < 1 + |(mode.2 : ℝ)|) _))
    (annularFrequency_pos mode)

def negativeTraceWeight (parameters : PhaseParameters) (angular cell : ℕ)
    (mode : ℤ × ℤ) : ℝ :=
  Real.sqrt (negativeTraceWeightSq parameters angular cell mode)

def positiveTraceWeight (parameters : PhaseParameters) (angular cell : ℕ)
    (mode : ℤ × ℤ) : ℝ :=
  Real.sqrt (positiveTraceWeightSq parameters angular cell mode)

theorem negativeTraceWeight_pos (parameters : PhaseParameters) (angular cell : ℕ)
    (mode : ℤ × ℤ) : 0 < negativeTraceWeight parameters angular cell mode :=
  Real.sqrt_pos.2 (negativeTraceWeightSq_pos parameters angular cell mode)

theorem positiveTraceWeight_pos (parameters : PhaseParameters) (angular cell : ℕ)
    (mode : ℤ × ℤ) : 0 < positiveTraceWeight parameters angular cell mode :=
  Real.sqrt_pos.2 (positiveTraceWeightSq_pos parameters angular cell mode)

/-- Complete AH16 negative-half trace coordinates. The parameters and orders
are encoded in the coordinate isometry, as for the accepted boundary grades. -/
abbrev NegativeTrace (_parameters : PhaseParameters) (_angular _cell dimension : ℕ) :=
  lp (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2

/-- Complete AH16 positive-half trace coordinates. -/
abbrev PositiveTrace (_parameters : PhaseParameters) (_angular _cell dimension : ℕ) :=
  lp (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2

def negativeTraceCoefficient {dimension : ℕ} (parameters : PhaseParameters)
    (angular cell : ℕ) (field : NegativeTrace parameters angular cell dimension)
    (mode : ℤ × ℤ) : ComplexEuclidean dimension :=
  ((negativeTraceWeight parameters angular cell mode : ℂ)⁻¹) • field mode

def positiveTraceCoefficient {dimension : ℕ} (parameters : PhaseParameters)
    (angular cell : ℕ) (field : PositiveTrace parameters angular cell dimension)
    (mode : ℤ × ℤ) : ComplexEuclidean dimension :=
  ((positiveTraceWeight parameters angular cell mode : ℂ)⁻¹) • field mode

theorem negativeTrace_weighted {dimension : ℕ} (parameters : PhaseParameters)
    (angular cell : ℕ) (field : NegativeTrace parameters angular cell dimension)
    (mode : ℤ × ℤ) :
    (negativeTraceWeight parameters angular cell mode : ℂ) •
        negativeTraceCoefficient parameters angular cell field mode = field mode :=
  smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr
    (negativeTraceWeight_pos parameters angular cell mode).ne') _

theorem positiveTrace_weighted {dimension : ℕ} (parameters : PhaseParameters)
    (angular cell : ℕ) (field : PositiveTrace parameters angular cell dimension)
    (mode : ℤ × ℤ) :
    (positiveTraceWeight parameters angular cell mode : ℂ) •
        positiveTraceCoefficient parameters angular cell field mode = field mode :=
  smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr
    (positiveTraceWeight_pos parameters angular cell mode).ne') _

theorem negativeTrace_norm_sq {dimension : ℕ} (parameters : PhaseParameters)
    (angular cell : ℕ) (field : NegativeTrace parameters angular cell dimension) :
    ‖field‖ ^ 2 = ∑' mode : ℤ × ℤ,
      negativeTraceWeightSq parameters angular cell mode *
        ‖negativeTraceCoefficient parameters angular cell field mode‖ ^ 2 := by
  have normFormula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at normFormula
  rw [normFormula]
  apply tsum_congr
  intro mode
  rw [← negativeTrace_weighted parameters angular cell field mode, norm_smul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (negativeTraceWeight_pos parameters angular cell mode), mul_pow]
  unfold negativeTraceWeight
  rw [
    Real.sq_sqrt (negativeTraceWeightSq_pos parameters angular cell mode).le]

theorem positiveTrace_norm_sq {dimension : ℕ} (parameters : PhaseParameters)
    (angular cell : ℕ) (field : PositiveTrace parameters angular cell dimension) :
    ‖field‖ ^ 2 = ∑' mode : ℤ × ℤ,
      positiveTraceWeightSq parameters angular cell mode *
        ‖positiveTraceCoefficient parameters angular cell field mode‖ ^ 2 := by
  have normFormula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at normFormula
  rw [normFormula]
  apply tsum_congr
  intro mode
  rw [← positiveTrace_weighted parameters angular cell field mode, norm_smul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (positiveTraceWeight_pos parameters angular cell mode), mul_pow]
  unfold positiveTraceWeight
  rw [
    Real.sq_sqrt (positiveTraceWeightSq_pos parameters angular cell mode).le]

theorem negativeTrace_complete {dimension : ℕ} (parameters : PhaseParameters)
    (angular cell : ℕ) :
    IsComplete (Set.univ : Set (NegativeTrace parameters angular cell dimension)) :=
  isComplete_univ

theorem positiveTrace_complete {dimension : ℕ} (parameters : PhaseParameters)
    (angular cell : ℕ) :
    IsComplete (Set.univ : Set (PositiveTrace parameters angular cell dimension)) :=
  isComplete_univ

end Grad.BoundaryKernelAction
