import BKC19UniformKernelMoments

noncomputable section

set_option maxHeartbeats 800000
set_option autoImplicit false

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Allocation Grad.ActualCurrentPrimitives

/-- The literal physical arguments, before imposing the original low ball. -/
abbrev BoundaryReconstructionData (parameters : PhaseParameters) :=
  ℝ × ℝ × ℝ × ℝ × ℝ × ACore parameters 3

namespace BoundaryReconstructionData

variable {parameters : PhaseParameters}

abbrev rho (data : BoundaryReconstructionData parameters) : ℝ := data.1
abbrev alpha (data : BoundaryReconstructionData parameters) : ℝ := data.2.1
abbrev delta (data : BoundaryReconstructionData parameters) : ℝ := data.2.2.1
abbrev parameter (data : BoundaryReconstructionData parameters) : ℝ := data.2.2.2.1
abbrev epsilon (data : BoundaryReconstructionData parameters) : ℝ := data.2.2.2.2.1
abbrev field (data : BoundaryReconstructionData parameters) : ACore parameters 3 := data.2.2.2.2.2

end BoundaryReconstructionData

/-- Exactly the existing B7 ball and compact parameter inequalities. -/
def BoundaryReconstructionValid (parameters : PhaseParameters) (L compactRadius : ℝ)
    (data : BoundaryReconstructionData parameters) : Prop :=
  physicalBudget parameters data.field data.rho data.epsilon 7 ≤
      actualMassInverseLowRadius parameters L compactRadius ∧
    0 ≤ compactRadius ∧ |data.alpha| ≤ compactRadius ∧
      |data.delta| ≤ compactRadius ∧ |data.parameter| ≤ compactRadius

abbrev BoundaryReconstructionState (parameters : PhaseParameters) (L compactRadius : ℝ) :=
  {data : BoundaryReconstructionData parameters // BoundaryReconstructionValid parameters L compactRadius data}

namespace BoundaryReconstructionState

variable {parameters : PhaseParameters} {L compactRadius : ℝ}

abbrev rho (state : BoundaryReconstructionState parameters L compactRadius) : ℝ := state.val.rho
abbrev alpha (state : BoundaryReconstructionState parameters L compactRadius) : ℝ := state.val.alpha
abbrev delta (state : BoundaryReconstructionState parameters L compactRadius) : ℝ := state.val.delta
abbrev parameter (state : BoundaryReconstructionState parameters L compactRadius) : ℝ := state.val.parameter
abbrev epsilon (state : BoundaryReconstructionState parameters L compactRadius) : ℝ := state.val.epsilon
abbrev field (state : BoundaryReconstructionState parameters L compactRadius) : ACore parameters 3 := state.val.field

theorem small (state : BoundaryReconstructionState parameters L compactRadius) :
    physicalBudget parameters state.field state.rho state.epsilon 7 ≤
      actualMassInverseLowRadius parameters L compactRadius := state.property.1

theorem compactNonnegative (state : BoundaryReconstructionState parameters L compactRadius) :
    0 ≤ compactRadius := state.property.2.1

theorem alphaSmall (state : BoundaryReconstructionState parameters L compactRadius) :
    |state.alpha| ≤ compactRadius := state.property.2.2.1

theorem deltaSmall (state : BoundaryReconstructionState parameters L compactRadius) :
    |state.delta| ≤ compactRadius := state.property.2.2.2.1

theorem parameterSmall (state : BoundaryReconstructionState parameters L compactRadius) :
    |state.parameter| ≤ compactRadius := state.property.2.2.2.2

def of (rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualMassInverseLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius) (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius) (parameterSmall : |parameter| ≤ compactRadius) :
    BoundaryReconstructionState parameters L compactRadius :=
  ⟨⟨rho, alpha, delta, parameter, epsilon, field⟩,
    small, compactNonnegative, alphaSmall, deltaSmall, parameterSmall⟩

theorem firstSmall (state : BoundaryReconstructionState parameters L compactRadius) :
    physicalBudget parameters state.field state.rho state.epsilon 7 ≤
      actualEncodedFirstLowRadius parameters L compactRadius :=
  state.small.trans (actualMassInverseLowRadius_le_first parameters L compactRadius)

theorem gaugeSmall (state : BoundaryReconstructionState parameters L compactRadius) :
    physicalBudget parameters state.field state.rho state.epsilon 6 ≤
      actualGaugeInverseLowRadius parameters L compactRadius :=
  (physicalBudget_monotone parameters state.field state.rho state.epsilon (by omega : 6 ≤ 7)).trans
    (state.firstSmall.trans (actualEncodedFirstLowRadius_le_gauge parameters L compactRadius))

theorem coefficientSmall (state : BoundaryReconstructionState parameters L compactRadius) :
    physicalBudget parameters state.field state.rho state.epsilon 6 ≤
      originalCoefficientLowRadius parameters L :=
  state.gaugeSmall.trans (actualGaugeInverseLowRadius_le_original parameters L compactRadius)

def size (state : BoundaryReconstructionState parameters L compactRadius) (moment : ℕ) : ℝ :=
  1 + physicalBudget parameters state.field state.rho state.epsilon (moment + 7)

theorem one_le_size (state : BoundaryReconstructionState parameters L compactRadius) (moment : ℕ) :
    1 ≤ state.size moment := by
  unfold size
  linarith [physicalBudget_nonnegative parameters state.field state.rho state.epsilon (moment + 7)]

theorem size_nonnegative (state : BoundaryReconstructionState parameters L compactRadius) (moment : ℕ) :
    0 ≤ state.size moment := zero_le_one.trans (state.one_le_size moment)

theorem size_zero_le (state : BoundaryReconstructionState parameters L compactRadius) :
    state.size 0 ≤ 1 + actualMassInverseLowRadius parameters L compactRadius :=
  add_le_add le_rfl state.small

theorem budget_le_size (state : BoundaryReconstructionState parameters L compactRadius)
    (moment order : ℕ) (order_le : order ≤ moment + 7) :
    physicalBudget parameters state.field state.rho state.epsilon order ≤ state.size moment := by
  apply (physicalBudget_monotone parameters state.field state.rho state.epsilon order_le).trans
  unfold size
  linarith

end BoundaryReconstructionState

abbrev PhysicalKernelMoments (parameters : PhaseParameters) (L compactRadius : ℝ)
    {input output : ℕ}
    (family : BoundaryReconstructionState parameters L compactRadius →
      FullTwoFrequencyKernel parameters input output) : Prop :=
  UniformKernelMoments parameters BoundaryReconstructionState.size family

theorem PhysicalKernelMoments.fixed (parameters : PhaseParameters) (L compactRadius : ℝ)
    {input output : ℕ} (kernel : FullTwoFrequencyKernel parameters input output) :
    PhysicalKernelMoments parameters L compactRadius (fun _ => kernel) :=
  UniformKernelMoments.fixed BoundaryReconstructionState.one_le_size kernel

theorem PhysicalKernelMoments.comp {parameters : PhaseParameters} {L compactRadius : ℝ}
    {input middle output : ℕ}
    {outer : BoundaryReconstructionState parameters L compactRadius →
      FullTwoFrequencyKernel parameters middle output}
    {inner : BoundaryReconstructionState parameters L compactRadius →
      FullTwoFrequencyKernel parameters input middle}
    (houter : PhysicalKernelMoments parameters L compactRadius outer)
    (hinner : PhysicalKernelMoments parameters L compactRadius inner) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => fullKernelComposition (outer state) (inner state)) :=
  UniformKernelMoments.comp BoundaryReconstructionState.size_nonnegative
    (1 + actualMassInverseLowRadius parameters L compactRadius)
    (by linarith [actualMassInverseLowRadius_positive parameters L compactRadius])
    BoundaryReconstructionState.size_zero_le houter hinner

theorem actualForceBoundaryKernel_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) (kind : Fin 2) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualForceBoundaryKernel parameters L state.rho state.epsilon
        state.field kind state.coefficientSmall) := by
  intro moment
  let constant := 3 * Real.exp (parameters.sigma0 + parameters.gamma) *
    forceFourierConstant parameters L kind moment 0
  refine ⟨|constant|, abs_nonneg _, ?_⟩
  intro state
  apply (actualForceBoundaryKernel_moment_le parameters L state.rho state.epsilon
    state.field kind state.coefficientSmall moment).trans
  exact mul_le_mul (le_abs_self constant) (state.budget_le_size moment (moment + 6) (by omega))
    (physicalBudget_nonnegative parameters state.field state.rho state.epsilon _)
    (abs_nonneg constant)

theorem actualRotatedForceBoundaryKernel_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) (kind : Fin 2) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualRotatedForceBoundaryKernel parameters L state.rho state.epsilon
        state.field kind state.coefficientSmall) := by
  intro moment
  let constant := 3 * Real.exp (parameters.sigma0 + parameters.gamma) *
    forceFourierConstant parameters L kind (moment + 1) 0
  refine ⟨|constant|, abs_nonneg _, ?_⟩
  intro state
  apply (actualRotatedForceBoundaryKernel_moment_le parameters L state.rho state.epsilon
    state.field kind state.coefficientSmall moment).trans
  exact mul_le_mul (le_abs_self constant) (state.budget_le_size moment (moment + 7) le_rfl)
    (physicalBudget_nonnegative parameters state.field state.rho state.epsilon _)
    (abs_nonneg constant)

end Grad.BoundaryKernelAction
