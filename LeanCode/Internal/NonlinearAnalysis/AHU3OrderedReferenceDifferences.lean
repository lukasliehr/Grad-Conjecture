import AHU2ActualCoefficientVanishing

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryInverse
open Grad.GaugeCoefficients.Physical.Allocation

 theorem fullKernel_sub_self {input output : ℕ} {parameters : PhaseParameters}
    (kernel : FullTwoFrequencyKernel parameters input output) :
    fullKernelSub kernel kernel = fullZeroKernel parameters input output := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  simp

 theorem fullKernel_sub_zero {input output : ℕ} {parameters : PhaseParameters}
    (kernel : FullTwoFrequencyKernel parameters input output) :
    fullKernelSub kernel (fullZeroKernel parameters input output) = kernel := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  simp

/-- The ordered telescope retains which factor owns the high moment. -/
theorem fullKernel_composition_difference {input middle output : ℕ} {parameters : PhaseParameters}
    (outer referenceOuter : FullTwoFrequencyKernel parameters middle output)
    (inner referenceInner : FullTwoFrequencyKernel parameters input middle) :
    fullKernelSub (fullKernelComposition outer inner) (fullKernelComposition referenceOuter referenceInner) =
      fullKernelAdd (fullKernelComposition (fullKernelSub outer referenceOuter) inner)
        (fullKernelComposition referenceOuter (fullKernelSub inner referenceInner)) := by
  simp only [fullKernelSub, fullKernelComposition_add_outer, fullKernelComposition_add_inner,
    fullKernelComposition_neg_outer, fullKernelComposition_neg_inner]
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  simp only [fullKernelAdd_entry, fullKernelNeg_entry]
  abel

/-- Exact ordered resolvent identity, used only with the actual constructed inverses. -/
theorem fullKernel_inverse_difference {dimension : ℕ} {parameters : PhaseParameters}
    (actual reference inverse referenceInverse : FullTwoFrequencyKernel parameters dimension dimension)
    (left : fullKernelComposition inverse actual = fullIdentityKernel parameters dimension)
    (referenceRight : fullKernelComposition reference referenceInverse = fullIdentityKernel parameters dimension) :
    fullKernelSub inverse referenceInverse =
      fullKernelNeg (fullKernelComposition inverse
        (fullKernelComposition (fullKernelSub actual reference) referenceInverse)) := by
  simp only [fullKernelSub, fullKernelComposition_add_outer, fullKernelComposition_add_inner,
    fullKernelComposition_neg_outer, fullKernelComposition_neg_inner]
  rw [← fullKernelComposition_assoc, left, fullIdentityKernel_comp, referenceRight, fullKernel_comp_identity]
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  simp only [fullKernelAdd_entry, fullKernelNeg_entry]
  abel

@[simp] theorem fullZeroKernel_moment {input output : ℕ} (parameters : PhaseParameters)
    (moment : ℕ) : fullKernelMoment parameters moment (fullZeroKernel parameters input output) = 0 := by
  have entryZero : ∀ shift, (fullZeroKernel parameters input output).entryNorm shift = 0 := by
    intro shift
    apply le_antisymm
    · apply (fullZeroKernel parameters input output).entryNorm_le shift 0
      intro frequency
      simp
    · exact fullKernelEntryNorm_nonnegative _ _
  simp [fullKernelMoment, entryZero]

abbrev RadialReferenceDifference (parameters : PhaseParameters) (L compact : ℝ) {input output : ℕ}
    (actual reference : (state : AnnularReconstructionState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input output) : Prop :=
  RadialDeviationMoments parameters L compact (fun state r => fullKernelSub (actual state r) (reference state r))

theorem RadialReferenceDifference.refl (parameters : PhaseParameters) (L compact : ℝ) {input output : ℕ}
    (actual : (state : AnnularReconstructionState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input output) :
    RadialReferenceDifference parameters L compact actual actual := by
  intro moment
  refine ⟨0, le_rfl, ?_⟩
  intro state r
  simp [fullKernel_sub_self]

theorem RadialReferenceDifference.zero {parameters : PhaseParameters} {L compact : ℝ} {input output : ℕ}
    {actual : (state : AnnularReconstructionState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input output}
    (vanishing : RadialDeviationMoments parameters L compact actual) :
    RadialReferenceDifference parameters L compact actual
      (fun _ r => fullZeroKernel (radialKernelParameters parameters r) input output) := by
  simpa only [RadialReferenceDifference, fullKernel_sub_zero] using vanishing

theorem RadialReferenceDifference.comp {parameters : PhaseParameters} {L compact : ℝ}
    {input middle output : ℕ}
    {outer referenceOuter : (state : AnnularReconstructionState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r middle output}
    {inner referenceInner : (state : AnnularReconstructionState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input middle}
    (outerDifference : RadialReferenceDifference parameters L compact outer referenceOuter)
    (innerDifference : RadialReferenceDifference parameters L compact inner referenceInner)
    (innerRegular : RadialPhysicalMoments parameters L compact inner)
    (referenceOuterRegular : RadialPhysicalMoments parameters L compact referenceOuter) :
    RadialReferenceDifference parameters L compact
      (fun state r => fullKernelComposition (outer state r) (inner state r))
      (fun state r => fullKernelComposition (referenceOuter state r) (referenceInner state r)) := by
  have bound := (outerDifference.comp_regular innerRegular).add
    (RadialDeviationMoments.regular_comp referenceOuterRegular innerDifference)
  simpa only [RadialReferenceDifference, fullKernel_composition_difference] using bound

theorem RadialReferenceDifference.inverse {parameters : PhaseParameters} {L compact : ℝ} {dimension : ℕ}
    {actual reference inverse referenceInverse : (state : AnnularReconstructionState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r dimension dimension}
    (difference : RadialReferenceDifference parameters L compact actual reference)
    (inverseRegular : RadialPhysicalMoments parameters L compact inverse)
    (referenceInverseRegular : RadialPhysicalMoments parameters L compact referenceInverse)
    (left : ∀ state r, fullKernelComposition (inverse state r) (actual state r) =
      fullIdentityKernel (radialKernelParameters parameters r) dimension)
    (referenceRight : ∀ state r, fullKernelComposition (reference state r) (referenceInverse state r) =
      fullIdentityKernel (radialKernelParameters parameters r) dimension) :
    RadialReferenceDifference parameters L compact inverse referenceInverse := by
  have bound := (RadialDeviationMoments.regular_comp inverseRegular
    (difference.comp_regular referenceInverseRegular)).neg
  intro moment
  obtain ⟨constant, nonnegative, estimate⟩ := bound moment
  refine ⟨constant, nonnegative, ?_⟩
  intro state r
  dsimp only
  rw [fullKernel_inverse_difference _ _ _ _ (left state r) (referenceRight state r)]
  exact estimate state r

theorem RadialReferenceDifference.congr {parameters : PhaseParameters} {L compact : ℝ} {input output : ℕ}
    {actual reference actual' reference' : (state : AnnularReconstructionState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input output}
    (difference : RadialReferenceDifference parameters L compact actual reference)
    (ha : ∀ state r, actual state r = actual' state r)
    (hr : ∀ state r, reference state r = reference' state r) :
    RadialReferenceDifference parameters L compact actual' reference' := by
  have ea : actual = actual' := funext (fun state => funext (ha state))
  have er : reference = reference' := funext (fun state => funext (hr state))
  rwa [← ea, ← er]

theorem fullKernel_add_difference {input output : ℕ} {parameters : PhaseParameters}
    (a b c d : FullTwoFrequencyKernel parameters input output) :
    fullKernelSub (fullKernelAdd a b) (fullKernelAdd c d) =
      fullKernelAdd (fullKernelSub a c) (fullKernelSub b d) := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  simp only [fullKernelSub_entry, fullKernelAdd_entry]
  abel

theorem RadialReferenceDifference.add {parameters : PhaseParameters} {L compact : ℝ} {input output : ℕ}
    {a b c d : (state : AnnularReconstructionState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input output}
    (first : RadialReferenceDifference parameters L compact a c)
    (second : RadialReferenceDifference parameters L compact b d) :
    RadialReferenceDifference parameters L compact
      (fun state r => fullKernelAdd (a state r) (b state r))
      (fun state r => fullKernelAdd (c state r) (d state r)) := by
  have bound := UniformRadialKernelMoments.add first second
  simpa only [RadialReferenceDifference, fullKernel_add_difference] using bound

theorem RadialReferenceDifference.neg {parameters : PhaseParameters} {L compact : ℝ} {input output : ℕ}
    {a b : (state : AnnularReconstructionState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input output}
    (difference : RadialReferenceDifference parameters L compact a b) :
    RadialReferenceDifference parameters L compact
      (fun state r => fullKernelNeg (a state r)) (fun state r => fullKernelNeg (b state r)) := by
  have equality : ∀ state r, fullKernelSub (fullKernelNeg (a state r)) (fullKernelNeg (b state r)) =
      fullKernelNeg (fullKernelSub (a state r) (b state r)) := by
    intro state r
    apply FullTwoFrequencyKernel.ext_entry
    intro shift frequency
    simp only [fullKernelSub_entry, fullKernelNeg_entry]
    abel
  simpa only [RadialReferenceDifference, equality] using UniformRadialKernelMoments.neg difference

theorem RadialReferenceDifference.sub {parameters : PhaseParameters} {L compact : ℝ} {input output : ℕ}
    {a b c d : (state : AnnularReconstructionState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input output}
    (first : RadialReferenceDifference parameters L compact a c)
    (second : RadialReferenceDifference parameters L compact b d) :
    RadialReferenceDifference parameters L compact
      (fun state r => fullKernelSub (a state r) (b state r))
      (fun state r => fullKernelSub (c state r) (d state r)) := first.add second.neg

theorem RadialReferenceDifference.left {parameters : PhaseParameters} {L compact : ℝ}
    {input middle output : ℕ}
    {outer : (state : AnnularReconstructionState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r middle output}
    {inner reference : (state : AnnularReconstructionState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input middle}
    (outerRegular : RadialPhysicalMoments parameters L compact outer)
    (difference : RadialReferenceDifference parameters L compact inner reference) :
    RadialReferenceDifference parameters L compact
      (fun state r => fullKernelComposition (outer state r) (inner state r))
      (fun state r => fullKernelComposition (outer state r) (reference state r)) := by
  simpa only [RadialReferenceDifference, fullKernelSub, fullKernelComposition_add_inner,
    fullKernelComposition_neg_inner] using RadialDeviationMoments.regular_comp outerRegular difference

theorem RadialReferenceDifference.right {parameters : PhaseParameters} {L compact : ℝ}
    {input middle output : ℕ}
    {outer reference : (state : AnnularReconstructionState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r middle output}
    {inner : (state : AnnularReconstructionState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input middle}
    (difference : RadialReferenceDifference parameters L compact outer reference)
    (innerRegular : RadialPhysicalMoments parameters L compact inner) :
    RadialReferenceDifference parameters L compact
      (fun state r => fullKernelComposition (outer state r) (inner state r))
      (fun state r => fullKernelComposition (reference state r) (inner state r)) := by
  simpa only [RadialReferenceDifference, fullKernelSub, fullKernelComposition_add_outer,
    fullKernelComposition_neg_outer] using difference.comp_regular innerRegular

theorem RadialReferenceDifference.add_right {parameters : PhaseParameters} {L compact : ℝ}
    {input output : ℕ}
    (actual : (state : AnnularReconstructionState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input output)
    {perturbation : (state : AnnularReconstructionState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input output}
    (vanishing : RadialDeviationMoments parameters L compact perturbation) :
    RadialReferenceDifference parameters L compact
      (fun state r => fullKernelAdd (actual state r) (perturbation state r)) actual := by
  have bound := (RadialReferenceDifference.refl parameters L compact actual).add (RadialReferenceDifference.zero vanishing)
  apply bound.congr (fun _ _ => rfl)
  intro state r
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  simp

theorem RadialReferenceDifference.sub_right {parameters : PhaseParameters} {L compact : ℝ}
    {input output : ℕ}
    (actual : (state : AnnularReconstructionState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input output)
    {perturbation : (state : AnnularReconstructionState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r input output}
    (vanishing : RadialDeviationMoments parameters L compact perturbation) :
    RadialReferenceDifference parameters L compact
      (fun state r => fullKernelSub (actual state r) (perturbation state r)) actual :=
  RadialReferenceDifference.add_right actual vanishing.neg

end Grad.AnnularReconstruction
