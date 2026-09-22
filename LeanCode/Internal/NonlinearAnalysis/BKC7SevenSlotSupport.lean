import BKC6ActualFirstInverseSupport

noncomputable section

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.Allocation

theorem fullNegativeKernelAction_smul {input output : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ) (scalar : ℂ)
    (kernel : FullTwoFrequencyKernel parameters input output)
    (field : NegativeTrace parameters angular cell input) :
    fullNegativeKernelAction parameters angular cell (fullKernelSmul scalar kernel) field =
      scalar • fullNegativeKernelAction parameters angular cell kernel field := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  rw [negativeTraceCoefficient_smul]
  exact (fullNegativeKernelAction_coefficient_hasSum parameters angular cell
      (fullKernelSmul scalar kernel) field mode).unique
    (((fullNegativeKernelAction_coefficient_hasSum parameters angular cell kernel
      field mode).const_smul scalar).congr (fun shift => by
          simp only [fullKernelSmul_entry, smul_apply]))

theorem IsAngularMeanFree.smul {dimension : ℕ}
    {parameters : PhaseParameters} {angular cell : ℕ} (scalar : ℂ)
    {field : NegativeTrace parameters angular cell dimension}
    (supported : IsAngularMeanFree parameters angular cell field) :
    IsAngularMeanFree parameters angular cell (scalar • field) := by
  intro axial
  rw [negativeTraceCoefficient_smul, supported, smul_zero]

theorem sevenInputSlotKernel_action (parameters : PhaseParameters) (angular cell : ℕ)
    (slot : Fin 7) (input : SevenSlotTrace parameters angular cell) :
    fullNegativeKernelAction parameters angular cell (sevenInputSlotKernel parameters slot)
      (sevenSlotFlatten parameters angular cell input) = input slot := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  apply PiLp.ext
  intro coordinate
  have unique : coordinate = 0 := Fin.eq_zero coordinate
  subst coordinate
  rw [sevenInputSlotKernel, coordinateProjectionKernel_action_coefficient,
    sevenSlotFlatten_coefficient]

/-- The exact two mean-free conditions needed by AE17 on AH20's seven
slots. They are discharged from the original source range and mean-free xi
in the physical consumer, rather than imposed on arbitrary ambient sources. -/
def KnownSevenSlotSupport (parameters : PhaseParameters) (L : ℝ) (angular cell : ℕ)
    (input : SevenSlotTrace parameters angular cell) : Prop :=
  IsAngularMeanFree parameters angular cell (input 5) ∧
    IsAngularMeanFree parameters angular cell (input 6 + (L : ℂ)⁻¹ • input 2)

variable (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤
      actualGaugeInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius)
    (angular cell : ℕ)

theorem actualKnownEncodedD0Kernel_action_support
    (input : SevenSlotTrace parameters angular cell) :
    EncodedSupport parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualKnownEncodedD0Kernel parameters L rho alpha delta parameter epsilon
          compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)
        (sevenSlotFlatten parameters angular cell input)) := by
  unfold actualKnownEncodedD0Kernel firstCoordinateInjectionKernel
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
  apply coordinateInjectionKernel_action_encoded_zero
  rw [fullNegativeKernelAction_sub]
  apply IsAngularConstant.sub
  · rw [fullNegativeKernelAction_comp]
    exact angularMeanKernel_action_constant parameters angular cell _
  · rw [fullNegativeKernelAction_comp]
    exact angularMeanKernel_action_constant parameters angular cell _

theorem actualKnownEncodedD1Kernel_action_support
    (input : SevenSlotTrace parameters angular cell)
    (supported : KnownSevenSlotSupport parameters L angular cell input) :
    EncodedSupport parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualKnownEncodedD1Kernel parameters L rho alpha delta parameter epsilon
          compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)
        (sevenSlotFlatten parameters angular cell input)) := by
  unfold actualKnownEncodedD1Kernel secondCoordinateInjectionKernel
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
  apply coordinateInjectionKernel_action_encoded_one
  rw [fullNegativeKernelAction_sub, sevenInputSlotKernel_action]
  apply supported.1.sub
  rw [fullNegativeKernelAction_comp]
  exact angularMeanFreeKernel_action_meanFree parameters angular cell _

theorem actualKnownEncodedD2Kernel_action_support
    (input : SevenSlotTrace parameters angular cell)
    (supported : KnownSevenSlotSupport parameters L angular cell input) :
    EncodedSupport parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualKnownEncodedD2Kernel parameters L rho alpha delta parameter epsilon
          compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)
        (sevenSlotFlatten parameters angular cell input)) := by
  unfold actualKnownEncodedD2Kernel thirdCoordinateInjectionKernel
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
  apply coordinateInjectionKernel_action_encoded_two
  rw [fullNegativeKernelAction_sub, fullNegativeKernelAction_add,
    fullNegativeKernelAction_smul, sevenInputSlotKernel_action, sevenInputSlotKernel_action]
  apply supported.2.sub
  rw [fullNegativeKernelAction_comp]
  exact angularMeanFreeKernel_action_meanFree parameters angular cell _

theorem actualKnownEncodedDataKernel_action_support
    (input : SevenSlotTrace parameters angular cell)
    (supported : KnownSevenSlotSupport parameters L angular cell input) :
    EncodedSupport parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualKnownEncodedDataKernel parameters L rho alpha delta parameter epsilon
          compactRadius field small compactNonnegative alphaSmall deltaSmall parameterSmall)
        (sevenSlotFlatten parameters angular cell input)) := by
  unfold actualKnownEncodedDataKernel
  rw [fullNegativeKernelAction_add, fullNegativeKernelAction_add]
  exact (actualKnownEncodedD0Kernel_action_support parameters L rho alpha delta parameter
      epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall
      parameterSmall angular cell input).add
    ((actualKnownEncodedD1Kernel_action_support parameters L rho alpha delta parameter
      epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall
      parameterSmall angular cell input supported).add
      (actualKnownEncodedD2Kernel_action_support parameters L rho alpha delta parameter
        epsilon compactRadius field small compactNonnegative alphaSmall deltaSmall
        parameterSmall angular cell input supported))

end Grad.BoundaryKernelAction
