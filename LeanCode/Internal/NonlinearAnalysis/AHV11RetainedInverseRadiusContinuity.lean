import AHV10FrozenOriginalOuterInverseReuse

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.AnnularKernelContinuity
open Grad.GaugeCoefficients.Physical.Allocation Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives

/-- The retained row's missing matrix component is continuous in the original radius. -/
theorem radialRetainedForceDeviationKernel_regular (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) :
    RegularKernelFamily (fun r => radialRetainedForceDeviationKernel parameters L compact state.val r) := by
  constructor
  · intro shift mode
    refine rowMultiplicationEntry_continuous (X := RadialPoint) 3
      (fun r component frequency => radialRetainedForceBaseCoefficient parameters L compact state.val r component frequency) ?_ shift mode
    intro component frequency
    have continuous : Continuous (fun radius => polarEntryScalar parameters
        (forceMatrixFamily parameters L state.val.epsilon state.val.field)
        (forceMatrixFamily_coherent parameters L state.val.rho state.val.epsilon state.val.field state.val.low)
        0 component 0 radius frequency) :=
      continuous_iff_continuousAt.mpr fun radius =>
        (polarEntryScalar_hasDerivAt parameters _ _ 0 component 0 radius frequency).continuousAt
    exact continuous.comp continuous_subtype_val
  · intro moment
    obtain ⟨constant, nonnegative, bound⟩ := radialRetainedForceDeviationKernel_vanishingMoments parameters L compact moment
    exact ⟨constant * state.errorBudget moment,
      mul_nonneg nonnegative (physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon _),
      bound state⟩

theorem radialRetainedForceKernel_regular (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) :
    RegularKernelFamily (fun r => radialRetainedForceKernel parameters L compact state.val r) := by
  have equality : (fun r => radialRetainedForceKernel parameters L compact state.val r) =
      (fun r => fullKernelAdd
        (fullKernelAdd (radialRetainedForceDeviationKernel parameters L compact state.val r)
          (radialRetainedForceDeviationKernel parameters L compact state.val r))
        (circularRetainedForceKernel (radialKernelParameters parameters r))) := by
    funext r
    apply FullTwoFrequencyKernel.ext_entry
    intro shift mode
    simp only [radialRetainedForceKernel, radialRetainedForceDeviationKernel, circularRetainedForceKernel,
      fullKernelAdd_entry, fullKernelSmul_entry]
    module
  rw [equality]
  exact ((radialRetainedForceDeviationKernel_regular parameters L compact state).add
    (radialRetainedForceDeviationKernel_regular parameters L compact state)).add
      (fixedRadialKernel_regular parameters circularRetainedForceKernel
        (fun _ _ => (sameConstantMatrixKernel _ _ _ _ _).smul 2))

theorem radialRetainedHighAKernel_regular (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) :
    RegularKernelFamily (radialRetainedHighAKernel parameters L compact state) := by
  unfold radialRetainedHighAKernel radialNormalizedRetainedFirstRowKernel
  with_reducible repeat' first
    | exact radialNormalizedCovariantKernel_regular parameters L compact state
    | exact radialNormalizedRotatedCovariantKernel_regular parameters L compact state
    | exact radialRetainedForceKernel_regular parameters L compact state
    | exact scalarModeRadialKernel_regular parameters _ _ _ _
    | exact constantMatrixRadialKernel_regular parameters _ _ _
    | apply RegularKernelFamily.comp
    | apply RegularKernelFamily.sub
  all_goals first
    | exact scalarModeRadialKernel_regular parameters _ _ _ _
    | exact constantMatrixRadialKernel_regular parameters _ _ _

theorem radialRetainedPreconditionKernel_regular (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) :
    RegularKernelFamily (radialRetainedPreconditionKernel parameters L compact state) :=
  (scalarModeRadialKernel_regular parameters 1 retainedBInverseMultiplier _ retainedBInverseMultiplier_norm_le).comp
    ((radialRetainedHighAKernel_regular parameters L compact state).sub
      (scalarModeRadialKernel_regular parameters 1 retainedBMultiplier _ retainedBMultiplier_norm_le).neg)

/-- Continuity of the actual convergent inverse, from the same radius-uniform smallness. -/
theorem radialRetainedHighInverse_regular (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) :
    RegularKernelFamily (radialRetainedHighInverse parameters L compact state) := by
  unfold radialRetainedHighInverse radialRetainedAmbientInverse
  exact ((radialRetainedPreconditionKernel_regular parameters L compact state.val).negativeInverse
    (identityRadialKernel_regular parameters 1) (1 / 2) (by norm_num) (by norm_num)
    (radialRetainedPreconditionKernel_small parameters L compact state)).comp
      (scalarModeRadialKernel_regular parameters 1 retainedBInverseMultiplier _ retainedBInverseMultiplier_norm_le)

theorem radialRetainedInverseError_regular (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) :
    RegularKernelFamily (fun r => fullKernelAdd (radialRetainedHighInverse parameters L compact state r)
      (retainedBInverseKernel (radialKernelParameters parameters r))) :=
  (radialRetainedHighInverse_regular parameters L compact state).add
    (scalarModeRadialKernel_regular parameters 1 retainedBInverseMultiplier _ retainedBInverseMultiplier_norm_le)

end Grad.AnnularReconstruction
