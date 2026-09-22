import AHW1RetainedStateMomentAllocation

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.GaugeCoefficients.Physical.Allocation

abbrev RetainedReferenceDifference (parameters : PhaseParameters) (L compact : ℝ) {input output : ℕ}
    (actual reference : (state : RetainedInverseState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input output) : Prop :=
  RetainedDeviationMoments parameters L compact (fun state r => fullKernelSub (actual state r) (reference state r))

theorem RetainedReferenceDifference.refl (parameters : PhaseParameters) (L compact : ℝ) {input output : ℕ}
    (actual : (state : RetainedInverseState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input output) :
    RetainedReferenceDifference parameters L compact actual actual := by
  intro moment
  refine ⟨0, le_rfl, ?_⟩
  intro state r
  simp [fullKernel_sub_self]

theorem RetainedReferenceDifference.zero {parameters : PhaseParameters} {L compact : ℝ} {input output : ℕ}
    {actual : (state : RetainedInverseState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input output}
    (vanishing : RetainedDeviationMoments parameters L compact actual) :
    RetainedReferenceDifference parameters L compact actual
      (fun _ r => fullZeroKernel (radialKernelParameters parameters r) input output) := by
  simpa only [RetainedReferenceDifference, fullKernel_sub_zero] using vanishing

theorem RetainedReferenceDifference.comp {parameters : PhaseParameters} {L compact : ℝ}
    {input middle output : ℕ}
    {outer referenceOuter : (state : RetainedInverseState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r middle output}
    {inner referenceInner : (state : RetainedInverseState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input middle}
    (outerDifference : RetainedReferenceDifference parameters L compact outer referenceOuter)
    (innerDifference : RetainedReferenceDifference parameters L compact inner referenceInner)
    (innerRegular : RetainedPhysicalMoments parameters L compact inner)
    (referenceOuterRegular : RetainedPhysicalMoments parameters L compact referenceOuter) :
    RetainedReferenceDifference parameters L compact
      (fun state r => fullKernelComposition (outer state r) (inner state r))
      (fun state r => fullKernelComposition (referenceOuter state r) (referenceInner state r)) := by
  have bound := (outerDifference.comp_regular innerRegular).add
    (RetainedDeviationMoments.regular_comp referenceOuterRegular innerDifference)
  simpa only [RetainedReferenceDifference, fullKernel_composition_difference] using bound

theorem RetainedReferenceDifference.congr {parameters : PhaseParameters} {L compact : ℝ} {input output : ℕ}
    {actual reference actual' reference' : (state : RetainedInverseState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input output}
    (difference : RetainedReferenceDifference parameters L compact actual reference)
    (ha : ∀ state r, actual state r = actual' state r)
    (hr : ∀ state r, reference state r = reference' state r) :
    RetainedReferenceDifference parameters L compact actual' reference' := by
  have ea : actual = actual' := funext (fun state => funext (ha state))
  have er : reference = reference' := funext (fun state => funext (hr state))
  rwa [← ea, ← er]

theorem RetainedReferenceDifference.add {parameters : PhaseParameters} {L compact : ℝ} {input output : ℕ}
    {a b c d : (state : RetainedInverseState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input output}
    (first : RetainedReferenceDifference parameters L compact a c)
    (second : RetainedReferenceDifference parameters L compact b d) :
    RetainedReferenceDifference parameters L compact
      (fun state r => fullKernelAdd (a state r) (b state r))
      (fun state r => fullKernelAdd (c state r) (d state r)) := by
  have bound := UniformRadialKernelMoments.add first second
  simpa only [RetainedReferenceDifference, fullKernel_add_difference] using bound

theorem RetainedReferenceDifference.neg {parameters : PhaseParameters} {L compact : ℝ} {input output : ℕ}
    {a b : (state : RetainedInverseState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input output}
    (difference : RetainedReferenceDifference parameters L compact a b) :
    RetainedReferenceDifference parameters L compact
      (fun state r => fullKernelNeg (a state r)) (fun state r => fullKernelNeg (b state r)) := by
  have equality : ∀ state r, fullKernelSub (fullKernelNeg (a state r)) (fullKernelNeg (b state r)) =
      fullKernelNeg (fullKernelSub (a state r) (b state r)) := by
    intro state r
    apply FullTwoFrequencyKernel.ext_entry
    intro shift frequency
    simp only [fullKernelSub_entry, fullKernelNeg_entry]
    abel
  simpa only [RetainedReferenceDifference, equality] using UniformRadialKernelMoments.neg difference

theorem RetainedReferenceDifference.sub {parameters : PhaseParameters} {L compact : ℝ} {input output : ℕ}
    {a b c d : (state : RetainedInverseState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input output}
    (first : RetainedReferenceDifference parameters L compact a c)
    (second : RetainedReferenceDifference parameters L compact b d) :
    RetainedReferenceDifference parameters L compact
      (fun state r => fullKernelSub (a state r) (b state r))
      (fun state r => fullKernelSub (c state r) (d state r)) := first.add second.neg

theorem RetainedReferenceDifference.left {parameters : PhaseParameters} {L compact : ℝ}
    {input middle output : ℕ}
    {outer : (state : RetainedInverseState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r middle output}
    {inner reference : (state : RetainedInverseState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input middle}
    (outerRegular : RetainedPhysicalMoments parameters L compact outer)
    (difference : RetainedReferenceDifference parameters L compact inner reference) :
    RetainedReferenceDifference parameters L compact
      (fun state r => fullKernelComposition (outer state r) (inner state r))
      (fun state r => fullKernelComposition (outer state r) (reference state r)) := by
  simpa only [RetainedReferenceDifference, fullKernelSub, fullKernelComposition_add_inner,
    fullKernelComposition_neg_inner] using RetainedDeviationMoments.regular_comp outerRegular difference

theorem RetainedReferenceDifference.right {parameters : PhaseParameters} {L compact : ℝ}
    {input middle output : ℕ}
    {outer reference : (state : RetainedInverseState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r middle output}
    {inner : (state : RetainedInverseState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input middle}
    (difference : RetainedReferenceDifference parameters L compact outer reference)
    (innerRegular : RetainedPhysicalMoments parameters L compact inner) :
    RetainedReferenceDifference parameters L compact
      (fun state r => fullKernelComposition (outer state r) (inner state r))
      (fun state r => fullKernelComposition (reference state r) (inner state r)) := by
  simpa only [RetainedReferenceDifference, fullKernelSub, fullKernelComposition_add_outer,
    fullKernelComposition_neg_outer] using difference.comp_regular innerRegular

theorem RetainedReferenceDifference.add_right {parameters : PhaseParameters} {L compact : ℝ}
    {input output : ℕ}
    (actual : (state : RetainedInverseState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input output)
    {perturbation : (state : RetainedInverseState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input output}
    (vanishing : RetainedDeviationMoments parameters L compact perturbation) :
    RetainedReferenceDifference parameters L compact
      (fun state r => fullKernelAdd (actual state r) (perturbation state r)) actual := by
  have bound := (RetainedReferenceDifference.refl parameters L compact actual).add (RetainedReferenceDifference.zero vanishing)
  apply bound.congr (fun _ _ => rfl)
  intro state r
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  simp

theorem RetainedReferenceDifference.sub_right {parameters : PhaseParameters} {L compact : ℝ}
    {input output : ℕ}
    (actual : (state : RetainedInverseState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input output)
    {perturbation : (state : RetainedInverseState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input output}
    (vanishing : RetainedDeviationMoments parameters L compact perturbation) :
    RetainedReferenceDifference parameters L compact
      (fun state r => fullKernelSub (actual state r) (perturbation state r)) actual :=
  RetainedReferenceDifference.add_right actual vanishing.neg


theorem RetainedPhysicalMoments.fixed (parameters : PhaseParameters) (L compact : ℝ) {input output : ℕ}
    (family : (p : PhaseParameters) → FullTwoFrequencyKernel p input output)
    (same : ∀ first second, SameKernelEntries (family first) (family second)) :
    RetainedPhysicalMoments parameters L compact (fun _ r => family (radialKernelParameters parameters r)) :=
  UniformRadialKernelMoments.fixed (fun state => state.val.val.one_le_size) family same

theorem RetainedDeviationMoments.regular {parameters : PhaseParameters} {L compact : ℝ} {input output : ℕ}
    {family : (state : RetainedInverseState parameters L compact) → (r : RadialPoint) → RadialKernel parameters r input output}
    (bound : RetainedDeviationMoments parameters L compact family) : RetainedPhysicalMoments parameters L compact family := by
  intro moment
  obtain ⟨constant, nonnegative, bounded⟩ := bound moment
  refine ⟨constant, nonnegative, fun state r => (bounded state r).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ nonnegative
  change state.val.errorBudget moment ≤ 1 + state.val.errorBudget moment
  linarith

theorem RetainedReferenceDifference.actual_regular {parameters : PhaseParameters} {L compact : ℝ} {input output : ℕ}
    {actual reference : (state : RetainedInverseState parameters L compact) → (r : RadialPoint) → RadialKernel parameters r input output}
    (difference : RetainedReferenceDifference parameters L compact actual reference)
    (regular : RetainedPhysicalMoments parameters L compact reference) : RetainedPhysicalMoments parameters L compact actual := by
  have bounded := difference.regular.add regular
  have equality (state : RetainedInverseState parameters L compact) (r : RadialPoint) :
      fullKernelAdd (fullKernelSub (actual state r) (reference state r)) (reference state r) = actual state r := by
    apply FullTwoFrequencyKernel.ext_entry
    intro shift mode
    simp only [fullKernelSub_entry, fullKernelAdd_entry]
    abel
  simpa only [equality] using bounded

end Grad.AnnularReconstruction
