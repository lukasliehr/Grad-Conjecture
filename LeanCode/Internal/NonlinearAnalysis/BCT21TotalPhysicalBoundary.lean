import BCT20HighTotalKernelAction

noncomputable section

namespace Grad.ActualBoundaryPrimitives

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

theorem fullOneHighKernelAction_base_coefficient {input output : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FullTwoFrequencyKernel parameters input output)
    (high : NegativeTotalTrace parameters grade input) (low : NegativeTotalTrace parameters 0 input)
    (compatible : TotalTraceCompatible parameters grade high low) (mode : ℤ × ℤ) :
    negativeTotalCoefficient parameters grade (fullOneHighKernelAction parameters grade kernel high low) mode =
      negativeTraceCoefficient parameters 0 0 (fullNegativeKernelAction parameters 0 0 kernel low) mode := by
  rw [fullOneHighKernelAction_coefficient parameters grade kernel high low compatible,
    ← (fullNegativeKernelAction_coefficient_hasSum parameters 0 0 kernel low mode).tsum_eq]
  apply tsum_congr
  intro shift
  rw [compatible]
  simp only [negativeTotalCoefficient, negativeTotalWeight, pow_zero, one_mul, negativeTraceCoefficient]

variable (parameters : PhaseParameters)
  (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
  (small : physicalBudget parameters field rho epsilon 7 ≤ physicalBoundaryLowRadius parameters L compact)
  (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
  (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
  (grade : ℕ) (high : NegativeTotalTrace parameters grade 7) (low : NegativeTotalTrace parameters 0 7)
  (compatible : TotalTraceCompatible parameters grade high low)

/-- The same physical boundary in the exact total-grade P_R norm used in
AH19. Compatibility says that both inputs represent the same physical trace. -/
def actualTotalPhysicalBoundary : HighTotalBoundaryPrimitive parameters grade :=
  ⟨fullOneHighKernelAction parameters grade
    (actualDifferentiatedPhysicalBoundaryKernel parameters L rho alpha delta parameter epsilon compact
      field small compactNonnegative alphaSmall deltaSmall parameterSmall) high low, by
        unfold actualDifferentiatedPhysicalBoundaryKernel
        exact fullOneHighKernelAction_high parameters grade _ high low compatible⟩

theorem actualTotalPhysicalBoundary_derivative :
    IsTotalAngularDerivative parameters grade
      (highTotalBoundaryPrimitiveTrace parameters grade
        (actualTotalPhysicalBoundary parameters L rho alpha delta parameter epsilon compact
          field small compactNonnegative alphaSmall deltaSmall parameterSmall grade high low compatible))
      (fullOneHighKernelAction parameters grade
        (actualDifferentiatedPhysicalBoundaryKernel parameters L rho alpha delta parameter epsilon compact
          field small compactNonnegative alphaSmall deltaSmall parameterSmall) high low) :=
  highTotalBoundaryPrimitive_derivative parameters grade _

theorem actualTotalPhysicalBoundary_oneHigh_bound :
    ‖actualTotalPhysicalBoundary parameters L rho alpha delta parameter epsilon compact
        field small compactNonnegative alphaSmall deltaSmall parameterSmall grade high low compatible‖ ≤
      2 ^ grade *
        (fullKernelMoment parameters 1
            (actualDifferentiatedPhysicalBoundaryKernel parameters L rho alpha delta parameter epsilon compact
              field small compactNonnegative alphaSmall deltaSmall parameterSmall) * ‖high‖ +
          fullKernelMoment parameters (grade + 1)
            (actualDifferentiatedPhysicalBoundaryKernel parameters L rho alpha delta parameter epsilon compact
              field small compactNonnegative alphaSmall deltaSmall parameterSmall) * ‖low‖) :=
  fullOneHighKernelAction_bound parameters grade _ high low

/-- The total-grade extension has exactly the same physical Fourier
coefficients as the original boundary at base grade. -/
theorem actualTotalPhysicalBoundary_base_coefficient (mode : ℤ × ℤ) :
    negativeTotalCoefficient parameters grade
      (highTotalBoundaryPrimitiveTrace parameters grade
        (actualTotalPhysicalBoundary parameters L rho alpha delta parameter epsilon compact
          field small compactNonnegative alphaSmall deltaSmall parameterSmall grade high low compatible)) mode =
      negativeTraceCoefficient parameters 0 0
        (fullNegativeKernelAction parameters 0 0
          (actualExtendedPhysicalBoundaryKernel parameters L rho alpha delta parameter epsilon compact
            field small compactNonnegative alphaSmall deltaSmall parameterSmall) low) mode := by
  rw [highTotalBoundaryPrimitiveTrace, angularInverseKernel,
    scalarModeDiagonalKernel_total_coefficient]
  change angularInverseMultiplier mode • negativeTotalCoefficient parameters grade
    (fullOneHighKernelAction parameters grade _ high low) mode = _
  rw [fullOneHighKernelAction_base_coefficient parameters grade _ high low compatible,
    actualExtendedPhysicalBoundaryKernel, fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    angularInverseKernel, scalarModeDiagonalKernel_action_coefficient]

end Grad.ActualBoundaryPrimitives
