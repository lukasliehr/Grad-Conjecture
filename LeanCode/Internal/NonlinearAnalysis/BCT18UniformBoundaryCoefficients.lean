import BCT17OriginalSourceBoundaryConsumer
import BKC20PhysicalMomentFamilies

noncomputable section

namespace Grad.ActualBoundaryPrimitives

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

/-- The existing reconstruction state restricted to the single original
B7 ball used by the physical boundary. -/
abbrev PhysicalBoundaryState (parameters : PhaseParameters) (L compact : ℝ) :=
  {state : BoundaryReconstructionState parameters L compact //
    physicalBudget parameters state.field state.rho state.epsilon 7 ≤
      physicalBoundaryLowRadius parameters L compact}

namespace PhysicalBoundaryState

variable {parameters : PhaseParameters} {L compact : ℝ}

theorem coefficientSmall (state : PhysicalBoundaryState parameters L compact) :
    physicalBudget parameters state.val.field state.val.rho state.val.epsilon 6 ≤
      boundaryCoefficientLowRadius parameters L compact :=
  physicalBoundary_coefficient_small parameters L state.val.rho state.val.epsilon compact
    state.val.field state.property

end PhysicalBoundaryState

abbrev BoundaryKernelMoments (parameters : PhaseParameters) (L compact : ℝ)
    {input output : ℕ}
    (family : PhysicalBoundaryState parameters L compact →
      FullTwoFrequencyKernel parameters input output) : Prop :=
  UniformKernelMoments parameters (fun state => state.val.size) family

theorem BoundaryKernelMoments.of_reconstruction {parameters : PhaseParameters} {L compact : ℝ}
    {input output : ℕ}
    {family : BoundaryReconstructionState parameters L compact →
      FullTwoFrequencyKernel parameters input output}
    (bounded : PhysicalKernelMoments parameters L compact family) :
    BoundaryKernelMoments parameters L compact (fun state => family state.val) := by
  intro moment
  obtain ⟨constant, nonnegative, bound⟩ := bounded moment
  exact ⟨constant, nonnegative, fun state => bound state.val⟩

theorem BoundaryKernelMoments.fixed (parameters : PhaseParameters) (L compact : ℝ)
    {input output : ℕ} (kernel : FullTwoFrequencyKernel parameters input output) :
    BoundaryKernelMoments parameters L compact (fun _ => kernel) :=
  UniformKernelMoments.fixed (fun state => state.val.one_le_size) kernel

theorem BoundaryKernelMoments.comp {parameters : PhaseParameters} {L compact : ℝ}
    {input middle output : ℕ}
    {outer : PhysicalBoundaryState parameters L compact → FullTwoFrequencyKernel parameters middle output}
    {inner : PhysicalBoundaryState parameters L compact → FullTwoFrequencyKernel parameters input middle}
    (houter : BoundaryKernelMoments parameters L compact outer)
    (hinner : BoundaryKernelMoments parameters L compact inner) :
    BoundaryKernelMoments parameters L compact
      (fun state => fullKernelComposition (outer state) (inner state)) :=
  UniformKernelMoments.comp (fun state => state.val.size_nonnegative)
    (1 + actualMassInverseLowRadius parameters L compact)
    (by linarith [actualMassInverseLowRadius_positive parameters L compact])
    (fun state => state.val.size_zero_le) houter hinner

theorem actualBoundaryMultiplier_uniformMoments (parameters : PhaseParameters) (L compact : ℝ) :
    BoundaryKernelMoments parameters L compact
      (fun state => actualBoundaryMultiplier parameters L state.val.rho state.val.alpha state.val.delta
        state.val.parameter state.val.epsilon compact state.val.field state.val.compactNonnegative
        state.val.alphaSmall state.val.deltaSmall state.val.parameterSmall state.coefficientSmall) := by
  intro moment
  refine ⟨boundaryMultiplierConstant parameters L compact moment,
    boundaryMultiplierConstant_nonnegative parameters L compact moment, ?_⟩
  intro state
  apply (actualBoundaryMultiplier_moment parameters L state.val.rho state.val.alpha state.val.delta
    state.val.parameter state.val.epsilon compact state.val.field state.val.compactNonnegative
    state.val.alphaSmall state.val.deltaSmall state.val.parameterSmall state.coefficientSmall moment).trans
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
    (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon
      (by omega : moment + 5 ≤ moment + 7)))
    (boundaryMultiplierConstant_nonnegative parameters L compact moment)

theorem actualRotatedBoundaryMultiplier_uniformMoments (parameters : PhaseParameters) (L compact : ℝ) :
    BoundaryKernelMoments parameters L compact
      (fun state => actualRotatedBoundaryMultiplier parameters L state.val.rho state.val.alpha state.val.delta
        state.val.parameter state.val.epsilon compact state.val.field state.val.compactNonnegative
        state.val.alphaSmall state.val.deltaSmall state.val.parameterSmall state.coefficientSmall) := by
  intro moment
  refine ⟨boundaryMultiplierConstant parameters L compact (moment + 1),
    boundaryMultiplierConstant_nonnegative parameters L compact (moment + 1), ?_⟩
  intro state
  apply (actualRotatedBoundaryMultiplier_moment parameters L state.val.rho state.val.alpha state.val.delta
    state.val.parameter state.val.epsilon compact state.val.field state.val.compactNonnegative
    state.val.alphaSmall state.val.deltaSmall state.val.parameterSmall state.coefficientSmall moment).trans
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
    (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon
      (by omega : moment + 6 ≤ moment + 7)))
    (boundaryMultiplierConstant_nonnegative parameters L compact (moment + 1))

end Grad.ActualBoundaryPrimitives
