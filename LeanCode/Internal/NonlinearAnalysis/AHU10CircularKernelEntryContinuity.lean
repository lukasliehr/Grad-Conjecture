import AHU9LiteralCircularFourierFormula
import AHT10UniformNormalizedActions

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryInverse Grad.AnnularKernelContinuity
open Grad.GaugeCoefficients.Physical.Allocation

macro "ahu_same" : tactic => `(tactic|
  with_reducible repeat' first
    | exact sameEncodedJKernel _ _
    | exact sameEncodedRotationKernel _ _
    | exact sameUnknownQAKernel _ _
    | exact sameConstantMatrixKernel _ _ _ _ _
    | exact sameScalarModeDiagonalKernel _ _ _ _ _ _
    | exact sameFullIdentityKernel _ _ _
    | apply SameKernelEntries.add
    | apply SameKernelEntries.comp
    | apply SameKernelEntries.neg
    | apply SameKernelEntries.smul)

theorem sameCircularNormalizedCovariantKernel (first second : PhaseParameters) (L : ℝ) :
    SameKernelEntries (circularNormalizedCovariantKernel first L) (circularNormalizedCovariantKernel second L) := by
  unfold circularNormalizedCovariantKernel circularUnknownUKernel circularRecoveredMassKernel
    circularKnownAStarKernel circularKnownWKernel circularUnknownWKernel circularKnownEncodedDataKernel
    circularUnknownNKernel
  ahu_same
  all_goals first
    | exact sameConstantMatrixKernel first second _ _ _
    | exact sameScalarModeDiagonalKernel first second _ _ _ _

theorem sameCircularNormalizedRotatedCovariantKernel (first second : PhaseParameters) (L : ℝ) :
    SameKernelEntries (circularNormalizedRotatedCovariantKernel first L)
      (circularNormalizedRotatedCovariantKernel second L) := by
  unfold circularNormalizedRotatedCovariantKernel circularUnknownVKernel circularRecoveredMassKernel
    circularKnownRAStarKernel circularKnownWKernel circularUnknownWKernel circularKnownEncodedDataKernel
    circularUnknownNKernel
  ahu_same
  all_goals first
    | exact sameConstantMatrixKernel first second _ _ _
    | exact sameScalarModeDiagonalKernel first second _ _ _ _

theorem circularNormalizedCovariantKernel_entry_continuous (parameters : PhaseParameters) (L : ℝ)
    (shift mode : ℤ × ℤ) :
    Continuous (fun r : RadialPoint => (circularNormalizedCovariantKernel
      (radialKernelParameters parameters r) L).entry shift mode) := by
  have equality : (fun r : RadialPoint => (circularNormalizedCovariantKernel
      (radialKernelParameters parameters r) L).entry shift mode) =
      fun _ => (circularNormalizedCovariantKernel parameters L).entry shift mode := by
    funext r
    exact sameCircularNormalizedCovariantKernel _ _ L shift mode
  rw [equality]
  exact continuous_const

theorem circularNormalizedRotatedCovariantKernel_entry_continuous (parameters : PhaseParameters) (L : ℝ)
    (shift mode : ℤ × ℤ) :
    Continuous (fun r : RadialPoint => (circularNormalizedRotatedCovariantKernel
      (radialKernelParameters parameters r) L).entry shift mode) := by
  have equality : (fun r : RadialPoint => (circularNormalizedRotatedCovariantKernel
      (radialKernelParameters parameters r) L).entry shift mode) =
      fun _ => (circularNormalizedRotatedCovariantKernel parameters L).entry shift mode := by
    funext r
    exact sameCircularNormalizedRotatedCovariantKernel _ _ L shift mode
  rw [equality]
  exact continuous_const

end Grad.AnnularReconstruction
