import BKC18PhysicalRotationConsumer

noncomputable section

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace

/-- Uniform moment bounds with one prescribed high state factor. The
constant is chosen before the state, at each fixed envelope grade. -/
def UniformKernelMoments {Index : Type*} (parameters : PhaseParameters)
    {input output : ℕ} (size : Index → ℕ → ℝ)
    (family : Index → FullTwoFrequencyKernel parameters input output) : Prop :=
  ∀ moment, ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ state, fullKernelMoment parameters moment (family state) ≤ constant * size state moment

theorem UniformKernelMoments.fixed {Index : Type*} {parameters : PhaseParameters}
    {input output : ℕ} {size : Index → ℕ → ℝ}
    (one_le_size : ∀ state moment, 1 ≤ size state moment)
    (kernel : FullTwoFrequencyKernel parameters input output) :
    UniformKernelMoments parameters size (fun _ => kernel) := by
  intro moment
  refine ⟨fullKernelMoment parameters moment kernel,
    fullKernelMoment_nonnegative parameters moment kernel, ?_⟩
  intro state
  exact le_mul_of_one_le_right (fullKernelMoment_nonnegative parameters moment kernel)
    (one_le_size state moment)

theorem UniformKernelMoments.add {Index : Type*} {parameters : PhaseParameters}
    {input output : ℕ} {size : Index → ℕ → ℝ}
    {first second : Index → FullTwoFrequencyKernel parameters input output}
    (hfirst : UniformKernelMoments parameters size first)
    (hsecond : UniformKernelMoments parameters size second) :
    UniformKernelMoments parameters size (fun state => fullKernelAdd (first state) (second state)) := by
  intro moment
  obtain ⟨firstConstant, firstNonnegative, firstBound⟩ := hfirst moment
  obtain ⟨secondConstant, secondNonnegative, secondBound⟩ := hsecond moment
  refine ⟨firstConstant + secondConstant, add_nonneg firstNonnegative secondNonnegative, ?_⟩
  intro state
  exact (fullKernelAdd_moment_le parameters moment _ _).trans
    ((add_le_add (firstBound state) (secondBound state)).trans_eq (add_mul _ _ _).symm)

theorem UniformKernelMoments.neg {Index : Type*} {parameters : PhaseParameters}
    {input output : ℕ} {size : Index → ℕ → ℝ}
    {family : Index → FullTwoFrequencyKernel parameters input output}
    (bounded : UniformKernelMoments parameters size family) :
    UniformKernelMoments parameters size (fun state => fullKernelNeg (family state)) := by
  intro moment
  obtain ⟨constant, nonnegative, bound⟩ := bounded moment
  exact ⟨constant, nonnegative, fun state =>
    (fullKernelNeg_moment_le parameters moment _).trans (bound state)⟩

theorem UniformKernelMoments.sub {Index : Type*} {parameters : PhaseParameters}
    {input output : ℕ} {size : Index → ℕ → ℝ}
    {first second : Index → FullTwoFrequencyKernel parameters input output}
    (hfirst : UniformKernelMoments parameters size first)
    (hsecond : UniformKernelMoments parameters size second) :
    UniformKernelMoments parameters size (fun state => fullKernelSub (first state) (second state)) :=
  hfirst.add hsecond.neg

/-- Ordered composition uses high/low + low/high. The bound never multiplies
the two high state sizes. -/
theorem UniformKernelMoments.comp {Index : Type*} {parameters : PhaseParameters}
    {input middle output : ℕ} {size : Index → ℕ → ℝ}
    (size_nonnegative : ∀ state moment, 0 ≤ size state moment)
    (lowSize : ℝ) (lowSizeNonnegative : 0 ≤ lowSize)
    (lowSizeBound : ∀ state, size state 0 ≤ lowSize)
    {outer : Index → FullTwoFrequencyKernel parameters middle output}
    {inner : Index → FullTwoFrequencyKernel parameters input middle}
    (houter : UniformKernelMoments parameters size outer)
    (hinner : UniformKernelMoments parameters size inner) :
    UniformKernelMoments parameters size
      (fun state => fullKernelComposition (outer state) (inner state)) := by
  intro moment
  obtain ⟨outerHigh, outerHighNonnegative, outerHighBound⟩ := houter moment
  obtain ⟨innerHigh, innerHighNonnegative, innerHighBound⟩ := hinner moment
  obtain ⟨outerLow, outerLowNonnegative, outerLowBound⟩ := houter 0
  obtain ⟨innerLow, innerLowNonnegative, innerLowBound⟩ := hinner 0
  refine ⟨2 ^ moment * (outerHigh * (innerLow * lowSize) +
    (outerLow * lowSize) * innerHigh), by positivity, ?_⟩
  intro state
  have sizeNonnegative := size_nonnegative state moment
  have outerBase := (outerLowBound state).trans
    (mul_le_mul_of_nonneg_left (lowSizeBound state) outerLowNonnegative)
  have innerBase := (innerLowBound state).trans
    (mul_le_mul_of_nonneg_left (lowSizeBound state) innerLowNonnegative)
  apply (fullKernelComposition_moment_le moment (outer state) (inner state)).trans
  calc
    _ ≤ 2 ^ moment *
      ((outerHigh * size state moment) * (innerLow * lowSize) +
        (outerLow * lowSize) * (innerHigh * size state moment)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add
        (mul_le_mul (outerHighBound state) innerBase
          (fullKernelMoment_nonnegative parameters 0 _) (by positivity))
        (mul_le_mul outerBase (innerHighBound state)
          (fullKernelMoment_nonnegative parameters moment _) (by positivity))
    _ = _ := by ring

theorem UniformKernelMoments.negativeIdentityInverse
    {Index : Type*} {parameters : PhaseParameters} {dimension : ℕ}
    {size : Index → ℕ → ℝ} (one_le_size : ∀ state moment, 1 ≤ size state moment)
    {family : Index → FullTwoFrequencyKernel parameters dimension dimension}
    (bounded : UniformKernelMoments parameters size family)
    (lowBound : ∀ state, fullKernelMoment parameters 0 (family state) ≤ 1 / 2) :
    UniformKernelMoments parameters size
      (fun state => fullKernelNegativeIdentityInverse parameters (family state) (1 / 2)
        (lowBound state) (by norm_num)) := by
  intro moment
  obtain ⟨constant, nonnegative, bound⟩ := bounded moment
  have neumannNonnegative : 0 ≤ fullKernelNeumannConstant moment (1 / 2) := by
    unfold fullKernelNeumannConstant
    exact tsum_nonneg (fun _ => by positivity)
  refine ⟨fullKernelMoment parameters moment (fullIdentityKernel parameters dimension) +
    fullKernelNeumannConstant moment (1 / 2) * constant, by
      exact add_nonneg (fullKernelMoment_nonnegative parameters moment _)
        (mul_nonneg neumannNonnegative nonnegative), ?_⟩
  intro state
  apply (fullKernelNegativeIdentityInverse_moment_le parameters moment (family state)
    (1 / 2) (lowBound state) (by norm_num)).trans
  calc
    _ ≤ fullKernelMoment parameters moment (fullIdentityKernel parameters dimension) *
        size state moment +
      fullKernelNeumannConstant moment (1 / 2) * (constant * size state moment) := by
      exact add_le_add
        (le_mul_of_one_le_right (fullKernelMoment_nonnegative parameters moment _)
          (one_le_size state moment))
        (mul_le_mul_of_nonneg_left (bound state) neumannNonnegative)
    _ = _ := by ring

end Grad.BoundaryKernelAction
