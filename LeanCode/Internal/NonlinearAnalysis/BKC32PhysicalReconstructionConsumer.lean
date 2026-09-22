import BKC31PhysicalCoordinateIdentities
import BKC27EvaluatedOneHighAction

noncomputable section

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.Allocation
open Grad.AxisCore Grad.RealFixedRanges

/-- AF16's physical forward coordinate identity on the entire original
prescribed-source range. The input p is only mean-free, never restricted to
high angular modes. -/
theorem actualPhysicalCovariantTrace_correctedFlux_eq
    (parameters : PhaseParameters) (L compactRadius : ℝ)
    (state : BoundaryReconstructionState parameters L compactRadius) (angular cell : ℕ)
    (large : 3 ≤ angular + cell + 2)
    (flux x : NegativeTrace parameters angular cell 1)
    (fluxSupported : IsAngularMeanFree parameters angular cell flux)
    (fluxDerivative : IsAngularDerivative parameters angular cell flux x)
    (xi : PositiveTrace parameters angular cell 1)
    (source : sourceRange parameters (angular + cell + 2) large) :
    actualCorrectedFluxTrace parameters L state.rho state.epsilon state.field state.coefficientSmall
      angular cell
      (actualPhysicalCovariantTrace parameters L state.rho state.alpha state.delta state.parameter state.epsilon
        compactRadius state.field state.small state.compactNonnegative state.alphaSmall
        state.deltaSmall state.parameterSmall angular cell x xi source.val)
      (positiveToNegative parameters angular cell xi) = flux := by
  exact actualCovariantKernel_correctedFlux_eq parameters L compactRadius state angular cell
    (actualSevenSlotTrace parameters L angular cell x xi source.val) flux fluxSupported
    fluxDerivative (positiveToNegative_derivative parameters angular cell xi)

/-- The converse uses the same original source and retained scalar as the
forward construction; the actual extracted flux derivative recovers A. -/
theorem actualPhysicalCorrectedFlux_recovers_mass
    (parameters : PhaseParameters) (L compactRadius : ℝ)
    (state : BoundaryReconstructionState parameters L compactRadius) (angular cell : ℕ)
    (large : 3 ≤ angular + cell + 2)
    (mass x : NegativeTrace parameters angular cell 1)
    (massSupported : IsAngularMeanFree parameters angular cell mass)
    (xi : PositiveTrace parameters angular cell 1)
    (source : sourceRange parameters (angular + cell + 2) large)
    (extracted : IsAngularDerivative parameters angular cell
      (actualCorrectedFluxTrace parameters L state.rho state.epsilon state.field state.coefficientSmall
        angular cell
        (actualPreMassCovariantTrace parameters L compactRadius state angular cell mass
          (actualSevenSlotTrace parameters L angular cell x xi source.val))
        (positiveToNegative parameters angular cell xi)) x) :
    fullNegativeKernelAction parameters angular cell
      (actualRecoveredMassKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon
        compactRadius state.field state.small state.compactNonnegative state.alphaSmall
        state.deltaSmall state.parameterSmall)
      (sevenSlotFlatten parameters angular cell
        (actualSevenSlotTrace parameters L angular cell x xi source.val)) = mass := by
  have recovered := actualPreMassCorrectedFlux_recovers_mass parameters L compactRadius state angular cell
    mass (actualSevenSlotTrace parameters L angular cell x xi source.val) massSupported
    (positiveToNegative_derivative parameters angular cell xi) x extracted
  have firstSlot : actualSevenSlotTrace parameters L angular cell x xi source.val 0 = x := rfl
  simpa only [actualRecoveredMassKernel, actualMassRightHandKernel,
    fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply, fullNegativeKernelAction_sub,
    sevenInputSlotKernel_action, firstSlot] using recovered

/-- The evaluated one-high action is the full coefficient convolution on
slotwise compatible representations of the same seven physical traces. -/
theorem actualCovariantKernel_oneHigh_consumer
    (parameters : PhaseParameters) (L compactRadius : ℝ) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (state : BoundaryReconstructionState parameters L compactRadius)
        (high : SevenSlotTotalTrace parameters grade) (low : SevenSlotTotalTrace parameters 0),
        (∀ slot, TotalTraceCompatible parameters grade (high slot) (low slot)) →
        let kernel := actualCovariantKernel parameters L state.rho state.alpha state.delta state.parameter
          state.epsilon compactRadius state.field state.small state.compactNonnegative
          state.alphaSmall state.deltaSmall state.parameterSmall
        let output := fullOneHighKernelAction parameters grade kernel
          (sevenSlotFlatten parameters grade 0 high) (sevenSlotFlatten parameters 0 0 low)
        ‖output‖ ≤ constant *
          ((1 + physicalBudget parameters state.field state.rho state.epsilon 8) * ‖high‖ +
            (1 + physicalBudget parameters state.field state.rho state.epsilon (grade + 8)) * ‖low‖) ∧
        ∀ mode, HasSum (fun shift : ℤ × ℤ =>
          kernel.entry shift (twoFrequencyTranslation shift mode)
            (negativeTotalCoefficient parameters grade (sevenSlotFlatten parameters grade 0 high)
              (twoFrequencyTranslation shift mode)))
          (negativeTotalCoefficient parameters grade output mode) := by
  obtain ⟨constant, nonnegative, bound⟩ := actualCovariantKernel_oneHigh_bound parameters L compactRadius grade
  refine ⟨constant, nonnegative, ?_⟩
  intro state high low compatible
  refine ⟨bound state high low, ?_⟩
  intro mode
  exact fullOneHighKernelAction_coefficient_hasSum parameters grade _ _ _
    (sevenSlotFlatten_total_compatible parameters grade high low compatible) mode

/-- The corresponding evaluated genuine angular row, with the same original
analytic phase envelope and the same slotwise compatibility condition. -/
theorem actualRotatedCovariantKernel_oneHigh_consumer
    (parameters : PhaseParameters) (L compactRadius : ℝ) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (state : BoundaryReconstructionState parameters L compactRadius)
        (high : SevenSlotTotalTrace parameters grade) (low : SevenSlotTotalTrace parameters 0),
        (∀ slot, TotalTraceCompatible parameters grade (high slot) (low slot)) →
        let kernel := actualRotatedCovariantKernel parameters L state.rho state.alpha state.delta state.parameter
          state.epsilon compactRadius state.field state.small state.compactNonnegative
          state.alphaSmall state.deltaSmall state.parameterSmall
        let output := fullOneHighKernelAction parameters grade kernel
          (sevenSlotFlatten parameters grade 0 high) (sevenSlotFlatten parameters 0 0 low)
        ‖output‖ ≤ constant *
          ((1 + physicalBudget parameters state.field state.rho state.epsilon 8) * ‖high‖ +
            (1 + physicalBudget parameters state.field state.rho state.epsilon (grade + 8)) * ‖low‖) ∧
        ∀ mode, HasSum (fun shift : ℤ × ℤ =>
          kernel.entry shift (twoFrequencyTranslation shift mode)
            (negativeTotalCoefficient parameters grade (sevenSlotFlatten parameters grade 0 high)
              (twoFrequencyTranslation shift mode)))
          (negativeTotalCoefficient parameters grade output mode) := by
  obtain ⟨constant, nonnegative, bound⟩ := actualRotatedCovariantKernel_oneHigh_bound parameters L compactRadius grade
  refine ⟨constant, nonnegative, ?_⟩
  intro state high low compatible
  refine ⟨bound state high low, ?_⟩
  intro mode
  exact fullOneHighKernelAction_coefficient_hasSum parameters grade _ _ _
    (sevenSlotFlatten_total_compatible parameters grade high low compatible) mode

/-- On compatible total-grade representations the evaluated rotated action
is still the genuine angular derivative, not an independently assumed row. -/
theorem actualCovariantKernel_oneHigh_rotation
    (parameters : PhaseParameters) (L compactRadius : ℝ) (grade : ℕ)
    (state : BoundaryReconstructionState parameters L compactRadius)
    (high : SevenSlotTotalTrace parameters grade) (low : SevenSlotTotalTrace parameters 0)
    (compatible : ∀ slot, TotalTraceCompatible parameters grade (high slot) (low slot))
    (massSupported : IsAngularMeanFree parameters 0 0 (low 0))
    (scalarDerivative : IsAngularDerivative parameters 0 0 (low 3) (low 1)) (mode : ℤ × ℤ) :
    negativeTotalCoefficient parameters grade
      (fullOneHighKernelAction parameters grade
        (actualRotatedCovariantKernel parameters L state.rho state.alpha state.delta state.parameter
          state.epsilon compactRadius state.field state.small state.compactNonnegative
          state.alphaSmall state.deltaSmall state.parameterSmall)
        (sevenSlotFlatten parameters grade 0 high) (sevenSlotFlatten parameters 0 0 low)) mode =
      (Complex.I * (mode.1 : ℂ)) • negativeTotalCoefficient parameters grade
        (fullOneHighKernelAction parameters grade
          (actualCovariantKernel parameters L state.rho state.alpha state.delta state.parameter
            state.epsilon compactRadius state.field state.small state.compactNonnegative
            state.alphaSmall state.deltaSmall state.parameterSmall)
          (sevenSlotFlatten parameters grade 0 high) (sevenSlotFlatten parameters 0 0 low)) mode := by
  have paired := sevenSlotFlatten_total_compatible parameters grade high low compatible
  have base (kernel : FullTwoFrequencyKernel parameters 7 3) :
      negativeTotalCoefficient parameters grade
        (fullOneHighKernelAction parameters grade kernel
          (sevenSlotFlatten parameters grade 0 high) (sevenSlotFlatten parameters 0 0 low)) mode =
      negativeTraceCoefficient parameters 0 0
        (fullNegativeKernelAction parameters 0 0 kernel (sevenSlotFlatten parameters 0 0 low)) mode := by
    rw [fullOneHighKernelAction_coefficient parameters grade kernel _ _ paired,
      ← (fullNegativeKernelAction_coefficient_hasSum parameters 0 0 kernel _ mode).tsum_eq]
    apply tsum_congr
    intro shift
    rw [paired]
    simp only [negativeTotalCoefficient, negativeTotalWeight, pow_zero, one_mul, negativeTraceCoefficient]
  rw [base, base]
  exact actualCovariantKernel_derivative parameters L state.rho state.alpha state.delta state.parameter
    state.epsilon compactRadius state.field state.small state.compactNonnegative state.alphaSmall
    state.deltaSmall state.parameterSmall 0 0 low massSupported scalarDerivative mode

end Grad.BoundaryKernelAction
