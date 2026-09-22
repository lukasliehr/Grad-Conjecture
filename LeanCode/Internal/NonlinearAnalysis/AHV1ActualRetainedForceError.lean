import AHU13EvaluatedOneHighErrorConsumer

noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.SourceCollarCoefficients

/-- The omitted retained force row comes from the same actual force matrix. -/
def radialRetainedForceDeviationKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact) (r : RadialPoint) : RadialKernel parameters r 3 1 :=
  radialRowKernel parameters r 3
    (radialRetainedForceBaseCoefficient parameters L compact state r)
    (radialRetainedForceBaseCoefficient_moments parameters L compact state r)

theorem radialRetainedForceDeviationKernel_vanishingMoments
    (parameters : PhaseParameters) (L compact : ℝ) :
    RadialDeviationMoments parameters L compact
      (fun state r => radialRetainedForceDeviationKernel parameters L compact state.val r) := by
  intro moment
  let constant := Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
    (∑ component : Fin 3, polarEntryConstant 0 component moment 0) *
      |(forceMatrixProfile parameters L).deviation (moment + 1)|
  refine ⟨constant, mul_nonneg (mul_nonneg (Real.exp_pos _).le
    (Finset.sum_nonneg fun component _ => (polarEntryConstant_pos 0 component moment 0).le)) (abs_nonneg _), ?_⟩
  intro state r
  apply (radialRowKernel_moment_le parameters r 3 moment _ _).trans
  have familyBound : ‖forceMatrixFamily parameters L state.val.epsilon state.val.field (moment + 1)‖ ≤
      |(forceMatrixProfile parameters L).deviation (moment + 1)| * state.errorBudget moment := by
    apply (forceMatrixFamily_bound parameters L state.val.rho state.val.epsilon state.val.field state.val.low (moment + 1)).trans
    exact mul_le_mul (le_abs_self _) (physicalBudget_monotone parameters state.val.field
      state.val.rho state.val.epsilon (by omega))
      (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon _)
      (abs_nonneg _)
  have each (component : Fin 3) :
      (∑' shift, productMoment parameters moment r.val
        (radialRetainedForceBaseCoefficient parameters L compact state.val r component) shift) ≤
      polarEntryConstant 0 component moment 0 *
        (|(forceMatrixProfile parameters L).deviation (moment + 1)| * state.errorBudget moment) := by
    exact (polarEntryScalarMoment_bound parameters _ _ 0 component moment 0 r.val r.property.1 r.property.2).trans
      (mul_le_mul_of_nonneg_left familyBound (polarEntryConstant_pos 0 component moment 0).le)
  have summed := Finset.sum_le_sum (s := Finset.univ) fun component _ => each component
  apply (mul_le_mul_of_nonneg_left summed (Real.exp_pos _).le).trans_eq
  dsimp only [constant]
  rw [← Finset.sum_mul]
  ring

def circularRetainedForceKernel (parameters : PhaseParameters) : FullTwoFrequencyKernel parameters 3 1 :=
  fullKernelSmul 2 (coordinateProjectionKernel parameters 3 1)

theorem radialRetainedForceKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) :
    RadialReferenceDifference parameters L compact
      (fun state r => radialRetainedForceKernel parameters L compact state.val r)
      (fun _ r => circularRetainedForceKernel (radialKernelParameters parameters r)) := by
  have deviation := (radialRetainedForceDeviationKernel_vanishingMoments parameters L compact).add
    (radialRetainedForceDeviationKernel_vanishingMoments parameters L compact)
  have bound := RadialReferenceDifference.add_right
    (fun (_ : AnnularReconstructionState parameters L compact) r =>
      circularRetainedForceKernel (radialKernelParameters parameters r)) deviation
  apply bound.congr
  · intro state r
    apply FullTwoFrequencyKernel.ext_entry
    intro shift frequency
    simp only [radialRetainedForceKernel, circularRetainedForceKernel, fullKernelAdd_entry, fullKernelSmul_entry,
      radialRetainedForceDeviationKernel]
    module
  · intro state r
    rfl

theorem circularRetainedForceKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun _ r => circularRetainedForceKernel (radialKernelParameters parameters r)) :=
  RadialPhysicalMoments.fixed parameters L compact _
    (fun _ _ => (sameConstantMatrixKernel _ _ _ _ _).smul 2)

end Grad.AnnularReconstruction
