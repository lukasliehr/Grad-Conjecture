import BCT17OriginalSourceBoundaryConsumer

noncomputable section

namespace Grad.ActualBoundaryPrimitives

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction

theorem scalarModeDiagonalKernel_action_raw {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (multiplier : ℤ × ℤ → ℂ) (bound : ℝ) (bounded : ∀ mode, ‖multiplier mode‖ ≤ bound)
    (field : NegativeTrace parameters angular cell dimension) (mode : ℤ × ℤ) :
    fullNegativeKernelAction parameters angular cell
      (scalarModeDiagonalKernel parameters dimension multiplier bound bounded) field mode =
      multiplier mode • field mode := by
  rw [← negativeTrace_weighted parameters angular cell
    (fullNegativeKernelAction parameters angular cell
      (scalarModeDiagonalKernel parameters dimension multiplier bound bounded) field) mode,
    scalarModeDiagonalKernel_action_coefficient, smul_comm,
    negativeTrace_weighted]

theorem scalarModeDiagonalKernel_total_coefficient {dimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (multiplier : ℤ × ℤ → ℂ) (bound : ℝ) (bounded : ∀ mode, ‖multiplier mode‖ ≤ bound)
    (field : NegativeTotalTrace parameters grade dimension) (mode : ℤ × ℤ) :
    negativeTotalCoefficient parameters grade
      (fullNegativeKernelAction parameters 0 0
        (scalarModeDiagonalKernel parameters dimension multiplier bound bounded) field) mode =
      multiplier mode • negativeTotalCoefficient parameters grade field mode := by
  unfold negativeTotalCoefficient
  rw [scalarModeDiagonalKernel_action_raw]
  exact smul_comm _ _ _

def IsTotalAngularDerivative {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (field derivative : NegativeTotalTrace parameters grade dimension) : Prop :=
  ∀ mode, negativeTotalCoefficient parameters grade derivative mode =
    (Complex.I * (mode.1 : ℂ)) • negativeTotalCoefficient parameters grade field mode

def totalHighAngularSubmodule (parameters : PhaseParameters) (grade : ℕ) :
    Submodule ℂ (NegativeTotalTrace parameters grade 1) where
  carrier := {field | ∀ mode : ℤ × ℤ, |mode.1| < 3 →
    negativeTotalCoefficient parameters grade field mode = 0}
  zero_mem' := by
    intro mode _
    exact (negativeTotalCoefficientCLM parameters grade mode).map_zero
  add_mem' := by
    intro first second hfirst hsecond mode low
    rw [negativeTotalCoefficient_add, hfirst mode low, hsecond mode low, add_zero]
  smul_mem' := by
    intro scalar field supported mode low
    change (negativeTotalCoefficientCLM parameters grade mode) (scalar • field) = 0
    rw [map_smul, negativeTotalCoefficientCLM_apply, supported mode low, smul_zero]

theorem totalHighAngularSubmodule_closed (parameters : PhaseParameters) (grade : ℕ) :
    IsClosed (totalHighAngularSubmodule parameters grade : Set (NegativeTotalTrace parameters grade 1)) := by
  change IsClosed {field : NegativeTotalTrace parameters grade 1 |
    ∀ mode : ℤ × ℤ, |mode.1| < 3 → negativeTotalCoefficient parameters grade field mode = 0}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun mode => isClosed_iInter fun _ =>
    (negativeTotalCoefficientCLM (dimension := 1) parameters grade mode).isClosed_ker

/-- The high P_R carrier at AH19's total tangential grade. -/
abbrev HighTotalBoundaryPrimitive (parameters : PhaseParameters) (grade : ℕ) :=
  totalHighAngularSubmodule parameters grade

instance highTotalBoundaryPrimitive_complete (parameters : PhaseParameters) (grade : ℕ) :
    CompleteSpace (HighTotalBoundaryPrimitive parameters grade) :=
  (totalHighAngularSubmodule_closed parameters grade).completeSpace_coe

def highTotalBoundaryPrimitiveTrace (parameters : PhaseParameters) (grade : ℕ)
    (field : HighTotalBoundaryPrimitive parameters grade) : NegativeTotalTrace parameters grade 1 :=
  fullNegativeKernelAction parameters 0 0 (angularInverseKernel parameters 1) field.val

theorem highTotalBoundaryPrimitive_derivative (parameters : PhaseParameters) (grade : ℕ)
    (field : HighTotalBoundaryPrimitive parameters grade) :
    IsTotalAngularDerivative parameters grade
      (highTotalBoundaryPrimitiveTrace parameters grade field) field.val := by
  intro mode
  rw [highTotalBoundaryPrimitiveTrace, angularInverseKernel, scalarModeDiagonalKernel_total_coefficient,
    smul_smul, angularFrequency_mul_inverse]
  by_cases zero : mode.1 = 0
  · have low : |mode.1| < 3 := by rw [zero]; norm_num
    rw [field.property mode low, smul_zero]
  · simp only [angularMeanFreeMultiplier, if_neg zero, one_smul]

theorem negativeTotalTrace_norm_sq {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (field : NegativeTotalTrace parameters grade dimension) :
    ‖field‖ ^ 2 = ∑' mode : ℤ × ℤ, negativeTotalWeight parameters grade mode ^ 2 *
      ‖negativeTotalCoefficient parameters grade field mode‖ ^ 2 := by
  have normFormula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at normFormula
  rw [normFormula]
  apply tsum_congr
  intro mode
  rw [← negativeTotal_weighted parameters grade field mode, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (negativeTotalWeight_pos parameters grade mode), mul_pow]

theorem highTotalBoundaryPrimitive_norm_sq (parameters : PhaseParameters) (grade : ℕ)
    (field : HighTotalBoundaryPrimitive parameters grade) :
    ‖field‖ ^ 2 = ∑' mode : ℤ × ℤ,
      negativeTotalWeight parameters grade mode ^ 2 * |(mode.1 : ℝ)| ^ 2 *
        ‖negativeTotalCoefficient parameters grade
          (highTotalBoundaryPrimitiveTrace parameters grade field) mode‖ ^ 2 := by
  change ‖field.val‖ ^ 2 = _
  rw [negativeTotalTrace_norm_sq]
  apply tsum_congr
  intro mode
  rw [highTotalBoundaryPrimitive_derivative parameters grade field mode,
    norm_smul, norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast, mul_pow]
  ring

end Grad.ActualBoundaryPrimitives
