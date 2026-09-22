import BKC1SupportPredicates

noncomputable section

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.Ledger

@[simp] theorem negativeTraceCoefficient_add {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (first second : NegativeTrace parameters angular cell dimension) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell (first + second) mode =
      negativeTraceCoefficient parameters angular cell first mode +
        negativeTraceCoefficient parameters angular cell second mode := by
  simp [negativeTraceCoefficient, smul_add]

@[simp] theorem negativeTraceCoefficient_neg {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (field : NegativeTrace parameters angular cell dimension) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell (-field) mode =
      -negativeTraceCoefficient parameters angular cell field mode := by
  simp [negativeTraceCoefficient]

@[simp] theorem negativeTraceCoefficient_sub {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (first second : NegativeTrace parameters angular cell dimension) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell (first - second) mode =
      negativeTraceCoefficient parameters angular cell first mode -
        negativeTraceCoefficient parameters angular cell second mode := by
  simp only [sub_eq_add_neg, negativeTraceCoefficient_add, negativeTraceCoefficient_neg]

@[simp] theorem negativeTraceCoefficient_smul {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ) (scalar : ℂ)
    (field : NegativeTrace parameters angular cell dimension) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell (scalar • field) mode =
      scalar • negativeTraceCoefficient parameters angular cell field mode := by
  change _ • (scalar • field mode) = scalar • (_ • field mode)
  exact smul_comm _ scalar (field mode)

theorem fullNegativeKernelAction_add {input output : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (first second : FullTwoFrequencyKernel parameters input output)
    (field : NegativeTrace parameters angular cell input) :
    fullNegativeKernelAction parameters angular cell (fullKernelAdd first second) field =
      fullNegativeKernelAction parameters angular cell first field +
        fullNegativeKernelAction parameters angular cell second field := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  rw [negativeTraceCoefficient_add]
  exact (fullNegativeKernelAction_coefficient_hasSum parameters angular cell
      (fullKernelAdd first second) field mode).unique
    (((fullNegativeKernelAction_coefficient_hasSum parameters angular cell first
      field mode).add (fullNegativeKernelAction_coefficient_hasSum parameters
        angular cell second field mode)).congr (fun shift => by
          simp only [fullKernelAdd_entry, add_apply]))

theorem fullNegativeKernelAction_neg {input output : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FullTwoFrequencyKernel parameters input output)
    (field : NegativeTrace parameters angular cell input) :
    fullNegativeKernelAction parameters angular cell (fullKernelNeg kernel) field =
      -fullNegativeKernelAction parameters angular cell kernel field := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  rw [negativeTraceCoefficient_neg]
  exact (fullNegativeKernelAction_coefficient_hasSum parameters angular cell
      (fullKernelNeg kernel) field mode).unique
    (((fullNegativeKernelAction_coefficient_hasSum parameters angular cell kernel
      field mode).neg).congr (fun shift => by
          simp only [fullKernelNeg_entry, neg_apply]))

theorem fullNegativeKernelAction_sub {input output : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (first second : FullTwoFrequencyKernel parameters input output)
    (field : NegativeTrace parameters angular cell input) :
    fullNegativeKernelAction parameters angular cell (fullKernelSub first second) field =
      fullNegativeKernelAction parameters angular cell first field -
        fullNegativeKernelAction parameters angular cell second field := by
  simp only [fullKernelSub, fullNegativeKernelAction_add, fullNegativeKernelAction_neg,
    sub_eq_add_neg]

theorem modeDiagonalKernel_action_coefficient {input output : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (diagonal : (ℤ × ℤ) → (ComplexEuclidean input →L[ℂ] ComplexEuclidean output))
    (bound : ℝ) (bounded : ∀ mode, ‖diagonal mode‖ ≤ bound)
    (field : NegativeTrace parameters angular cell input) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell
        (fullNegativeKernelAction parameters angular cell
          (modeDiagonalKernel parameters input output diagonal bound bounded) field) mode =
      diagonal mode (negativeTraceCoefficient parameters angular cell field mode) := by
  rw [← (fullNegativeKernelAction_coefficient_hasSum parameters angular cell
    (modeDiagonalKernel parameters input output diagonal bound bounded) field mode).tsum_eq]
  rw [tsum_eq_single (0, 0) (by
    intro shift nonzero
    simp only [modeDiagonalKernel_entry, if_neg nonzero, zero_apply])]
  simp only [modeDiagonalKernel_entry, if_pos, twoFrequencyTranslation_apply,
    sub_zero]

theorem scalarModeDiagonalKernel_action_coefficient {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (multiplier : ℤ × ℤ → ℂ) (bound : ℝ)
    (bounded : ∀ mode, ‖multiplier mode‖ ≤ bound)
    (field : NegativeTrace parameters angular cell dimension) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell
        (fullNegativeKernelAction parameters angular cell
          (scalarModeDiagonalKernel parameters dimension multiplier bound bounded) field) mode =
      multiplier mode • negativeTraceCoefficient parameters angular cell field mode := by
  rw [scalarModeDiagonalKernel, modeDiagonalKernel_action_coefficient]
  rfl

theorem constantMatrixKernel_action_coefficient {input output : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (field : NegativeTrace parameters angular cell input) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell
        (fullNegativeKernelAction parameters angular cell
          (constantMatrixKernel parameters input output mapping) field) mode =
      mapping (negativeTraceCoefficient parameters angular cell field mode) :=
  modeDiagonalKernel_action_coefficient parameters angular cell _ _ _ field mode

theorem coordinateInjectionKernel_action_coefficient {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ) (coordinate : Fin dimension)
    (field : NegativeTrace parameters angular cell 1) (mode : ℤ × ℤ)
    (output : Fin dimension) :
    negativeTraceCoefficient parameters angular cell
        (fullNegativeKernelAction parameters angular cell
          (coordinateInjectionKernel parameters dimension coordinate) field) mode output =
      if output = coordinate then
        negativeTraceCoefficient parameters angular cell field mode 0 else 0 := by
  rw [coordinateInjectionKernel, constantMatrixKernel_action_coefficient]
  simp [matrixUnit_apply, operatorBasis, eq_comm]

theorem coordinateProjectionKernel_action_coefficient {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ) (coordinate : Fin dimension)
    (field : NegativeTrace parameters angular cell dimension) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell
        (fullNegativeKernelAction parameters angular cell
          (coordinateProjectionKernel parameters dimension coordinate) field) mode 0 =
      negativeTraceCoefficient parameters angular cell field mode coordinate := by
  rw [coordinateProjectionKernel, constantMatrixKernel_action_coefficient]
  simp [matrixUnit_apply, operatorBasis]

end Grad.BoundaryKernelAction
