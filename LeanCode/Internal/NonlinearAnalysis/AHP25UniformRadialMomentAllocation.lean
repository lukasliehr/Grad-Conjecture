import AHP24OriginalSevenSlotReconstruction

noncomputable section
set_option maxHeartbeats 1600000

namespace Grad.AnnularReconstruction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction

/-- Uniform moment bounds with one prescribed high state factor. The
constant is chosen before the state, at each fixed envelope grade. -/
def UniformRadialKernelMoments {Index : Type*} (parameters : PhaseParameters)
    {input output : ℕ} (size : Index → ℕ → ℝ)
    (family : (state : Index) → (r : RadialPoint) → RadialKernel parameters r input output) : Prop :=
  ∀ moment, ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ state r, fullKernelMoment (radialKernelParameters parameters r) moment (family state r) ≤ constant * size state moment

theorem UniformRadialKernelMoments.fixed {Index : Type*} {parameters : PhaseParameters}
    {input output : ℕ} {size : Index → ℕ → ℝ}
    (one_le_size : ∀ state moment, 1 ≤ size state moment)
    (family : (p : PhaseParameters) → FullTwoFrequencyKernel p input output)
    (same : ∀ first second, SameKernelEntries (family first) (family second)) :
    UniformRadialKernelMoments parameters size (fun _ r => family (radialKernelParameters parameters r)) := by
  intro moment
  refine ⟨fullKernelMoment (maximalKernelParameters parameters) moment
    (family (maximalKernelParameters parameters)), fullKernelMoment_nonnegative _ _ _, ?_⟩
  intro state r
  exact ((same _ _).radialMoment_le parameters r moment).trans
    (le_mul_of_one_le_right (fullKernelMoment_nonnegative _ _ _) (one_le_size state moment))

theorem UniformRadialKernelMoments.add {Index : Type*} {parameters : PhaseParameters}
    {input output : ℕ} {size : Index → ℕ → ℝ}
    {first second : (state : Index) → (r : RadialPoint) → RadialKernel parameters r input output}
    (hfirst : UniformRadialKernelMoments parameters size first)
    (hsecond : UniformRadialKernelMoments parameters size second) :
    UniformRadialKernelMoments parameters size (fun state r => fullKernelAdd (first state r) (second state r)) := by
  intro moment
  obtain ⟨firstConstant, firstNonnegative, firstBound⟩ := hfirst moment
  obtain ⟨secondConstant, secondNonnegative, secondBound⟩ := hsecond moment
  refine ⟨firstConstant + secondConstant, add_nonneg firstNonnegative secondNonnegative, ?_⟩
  intro state r
  exact (fullKernelAdd_moment_le (radialKernelParameters parameters r) moment _ _).trans
    ((add_le_add (firstBound state r) (secondBound state r)).trans_eq (add_mul _ _ _).symm)

theorem UniformRadialKernelMoments.neg {Index : Type*} {parameters : PhaseParameters}
    {input output : ℕ} {size : Index → ℕ → ℝ}
    {family : (state : Index) → (r : RadialPoint) → RadialKernel parameters r input output}
    (bounded : UniformRadialKernelMoments parameters size family) :
    UniformRadialKernelMoments parameters size (fun state r => fullKernelNeg (family state r)) := by
  intro moment
  obtain ⟨constant, nonnegative, bound⟩ := bounded moment
  exact ⟨constant, nonnegative, fun state r =>
    (fullKernelNeg_moment_le (radialKernelParameters parameters r) moment _).trans (bound state r)⟩

theorem UniformRadialKernelMoments.sub {Index : Type*} {parameters : PhaseParameters}
    {input output : ℕ} {size : Index → ℕ → ℝ}
    {first second : (state : Index) → (r : RadialPoint) → RadialKernel parameters r input output}
    (hfirst : UniformRadialKernelMoments parameters size first)
    (hsecond : UniformRadialKernelMoments parameters size second) :
    UniformRadialKernelMoments parameters size (fun state r => fullKernelSub (first state r) (second state r)) :=
  hfirst.add hsecond.neg

/-- Ordered composition uses high/low + low/high. The bound never multiplies
the two high state sizes. -/
theorem UniformRadialKernelMoments.comp {Index : Type*} {parameters : PhaseParameters}
    {input middle output : ℕ} {size : Index → ℕ → ℝ}
    (size_nonnegative : ∀ state moment, 0 ≤ size state moment)
    (lowSize : ℝ) (lowSizeNonnegative : 0 ≤ lowSize)
    (lowSizeBound : ∀ state, size state 0 ≤ lowSize)
    {outer : (state : Index) → (r : RadialPoint) → RadialKernel parameters r middle output}
    {inner : (state : Index) → (r : RadialPoint) → RadialKernel parameters r input middle}
    (houter : UniformRadialKernelMoments parameters size outer)
    (hinner : UniformRadialKernelMoments parameters size inner) :
    UniformRadialKernelMoments parameters size
      (fun state r => fullKernelComposition (outer state r) (inner state r)) := by
  intro moment
  obtain ⟨outerHigh, outerHighNonnegative, outerHighBound⟩ := houter moment
  obtain ⟨innerHigh, innerHighNonnegative, innerHighBound⟩ := hinner moment
  obtain ⟨outerLow, outerLowNonnegative, outerLowBound⟩ := houter 0
  obtain ⟨innerLow, innerLowNonnegative, innerLowBound⟩ := hinner 0
  refine ⟨2 ^ moment * (outerHigh * (innerLow * lowSize) +
    (outerLow * lowSize) * innerHigh), by positivity, ?_⟩
  intro state r
  have sizeNonnegative := size_nonnegative state moment
  have outerBase := (outerLowBound state r).trans
    (mul_le_mul_of_nonneg_left (lowSizeBound state) outerLowNonnegative)
  have innerBase := (innerLowBound state r).trans
    (mul_le_mul_of_nonneg_left (lowSizeBound state) innerLowNonnegative)
  apply (fullKernelComposition_moment_le moment (outer state r) (inner state r)).trans
  calc
    _ ≤ 2 ^ moment *
      ((outerHigh * size state moment) * (innerLow * lowSize) +
        (outerLow * lowSize) * (innerHigh * size state moment)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add
        (mul_le_mul (outerHighBound state r) innerBase
          (fullKernelMoment_nonnegative (radialKernelParameters parameters r) 0 _) (by positivity))
        (mul_le_mul outerBase (innerHighBound state r)
          (fullKernelMoment_nonnegative (radialKernelParameters parameters r) moment _) (by positivity))
    _ = _ := by ring

theorem UniformRadialKernelMoments.negativeIdentityInverse
    {Index : Type*} {parameters : PhaseParameters} {dimension : ℕ}
    {size : Index → ℕ → ℝ} (one_le_size : ∀ state moment, 1 ≤ size state moment)
    {family : (state : Index) → (r : RadialPoint) → RadialKernel parameters r dimension dimension}
    (bounded : UniformRadialKernelMoments parameters size family)
    (lowBound : ∀ state r, fullKernelMoment (radialKernelParameters parameters r) 0 (family state r) ≤ 1 / 2) :
    UniformRadialKernelMoments parameters size
      (fun state r => fullKernelNegativeIdentityInverse (radialKernelParameters parameters r) (family state r) (1 / 2)
        (lowBound state r) (by norm_num)) := by
  intro moment
  obtain ⟨constant, nonnegative, bound⟩ := bounded moment
  have neumannNonnegative : 0 ≤ fullKernelNeumannConstant moment (1 / 2) := by
    unfold fullKernelNeumannConstant
    exact tsum_nonneg (fun _ => by positivity)
  refine ⟨fullKernelMoment (maximalKernelParameters parameters) moment
    (fullIdentityKernel (maximalKernelParameters parameters) dimension) +
    fullKernelNeumannConstant moment (1 / 2) * constant, by
      exact add_nonneg (fullKernelMoment_nonnegative _ _ _)
        (mul_nonneg neumannNonnegative nonnegative), ?_⟩
  intro state r
  apply (fullKernelNegativeIdentityInverse_moment_le (radialKernelParameters parameters r) moment
    (family state r) (1 / 2) (lowBound state r) (by norm_num)).trans
  have identity := (sameFullIdentityKernel (radialKernelParameters parameters r)
    (maximalKernelParameters parameters) dimension).radialMoment_le parameters r moment
  calc
    _ ≤ fullKernelMoment (maximalKernelParameters parameters) moment
          (fullIdentityKernel (maximalKernelParameters parameters) dimension) * size state moment +
        fullKernelNeumannConstant moment (1 / 2) * (constant * size state moment) := by
      exact add_le_add
        (identity.trans (le_mul_of_one_le_right (fullKernelMoment_nonnegative _ _ _)
          (one_le_size state moment)))
        (mul_le_mul_of_nonneg_left (bound state r) neumannNonnegative)
    _ = _ := by ring

end Grad.AnnularReconstruction
