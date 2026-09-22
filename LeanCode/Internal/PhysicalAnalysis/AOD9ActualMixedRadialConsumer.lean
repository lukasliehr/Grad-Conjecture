import AOD8ActualAllRadialInduction

noncomputable section
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped ContDiff BigOperators Interval
namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints

/-- Literal high-sector mixed radial/angular energy. Excluded modes carry
zero, while every high coefficient retains its genuine within derivative. -/
def highRadialDerivativeEnergy (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (source : highDiskL2) (radial angular : ℕ) (mode : ℤ) : ℝ :=
  if mode ∈ lowAngularModes then 0 else
    |(mode : ℝ)| ^ (2 * angular) * actualRadialJetEnergy lower positive bounded parameter source radial mode

theorem highRadialDerivativeEnergy_nonnegative (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (source : highDiskL2) (radial angular : ℕ) (mode : ℤ) :
    0 ≤ highRadialDerivativeEnergy lower positive bounded parameter source radial angular mode :=
  ite_nonneg (le_refl 0) (mul_nonneg (pow_nonneg (abs_nonneg _) _)
    (actualRadialJetEnergy_nonnegative lower positive bounded parameter source radial mode))

theorem highRadialDerivativeEnergy_literal (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (source : highDiskL2) (radial angular : ℕ) (mode : ℤ) (high : mode ∉ lowAngularModes) :
    highRadialDerivativeEnergy lower positive bounded parameter source radial angular mode =
      |(mode : ℝ)| ^ (2 * angular) * ∫ radius in lower..1, radius *
        ‖iteratedDerivWithin radial (actualRadialValue lower positive bounded mode parameter source) (Icc lower 1) radius‖ ^ 2 :=
  if_neg high

/-- All mixed orders through s+2, with one constant C(s,K,a) and the actual
smooth source's original ordinary Hs norm, independent of angular cutoff. -/
theorem actualAllMixedRadial_finite (grade : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (ceiling : ℝ) : ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ parameter : ℝ, |parameter| ≤ ceiling → ∀ (source : highDiskL2) (core : ClosedJet 1),
      source.val = closedL2Core core → ∀ radial angular : ℕ, radial + angular ≤ grade + 2 → ∀ modes : Finset ℤ,
        (∑ mode ∈ modes, highRadialDerivativeEnergy lower positive bounded parameter source radial angular mode) ≤
          constant * ‖unitDiskCoreInto grade core‖ ^ 2 := by
  obtain ⟨constant, nonnegative, bound⟩ := actualAllRadial_finite grade lower positive bounded ceiling
  refine ⟨constant, nonnegative, ?_⟩
  intro parameter parameterBound source core same radial angular paid modes
  let highModes := modes.filter (fun mode => mode ∉ lowAngularModes)
  have high : ∀ mode ∈ highModes, mode ∉ lowAngularModes := fun _ member => (Finset.mem_filter.mp member).2
  have topBound := bound parameter parameterBound source core same radial (by omega) highModes high
  have lowerBound : (∑ mode ∈ highModes, |(mode : ℝ)| ^ (2 * angular) *
      actualRadialJetEnergy lower positive bounded parameter source radial mode) ≤
      ∑ mode ∈ highModes, mixedRadialEnergy grade radial (actualRadialJetEnergy lower positive bounded parameter source) mode := by
    apply Finset.sum_le_sum
    intro mode member
    have frequency : (1 : ℝ) ≤ |(mode : ℝ)| := by
      have square := highMode_sq mode (high mode member)
      nlinarith [abs_nonneg (mode : ℝ)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ frequency (by omega))
      (actualRadialJetEnergy_nonnegative lower positive bounded parameter source radial mode)
  have finite := lowerBound.trans topBound
  simpa only [highModes, Finset.sum_filter, highRadialDerivativeEnergy, ite_not] using finite

private theorem nonnegative_finite_total (energy : ℤ → ℝ) (constant : ℝ)
    (nonnegative : ∀ mode, 0 ≤ energy mode)
    (finite : ∀ modes : Finset ℤ, (∑ mode ∈ modes, energy mode) ≤ constant) :
    Summable energy ∧ (∑' mode : ℤ, energy mode) ≤ constant := by
  have summable := summable_of_sum_le nonnegative finite
  exact ⟨summable, summable.tsum_le_of_sum_le finite⟩

/-- The full closed-collar AN19 induction consumer: all genuine mixed
radial/angular derivatives through s+2 are collectively square summable
for the same constructed inverse. No unproved Sobolev representative or
higher-radial estimate is a premise. -/
theorem actualClosedCollarAllRadialDerivatives (grade : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (ceiling : ℝ) : ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ parameter : ℝ, |parameter| ≤ ceiling → ∀ (source : highDiskL2) (core : ClosedJet 1),
      source.val = closedL2Core core → ∀ radial angular : ℕ, radial + angular ≤ grade + 2 →
      (∀ mode : ℤ, mode ∉ lowAngularModes →
        highRadialDerivativeEnergy lower positive bounded parameter source radial angular mode =
          |(mode : ℝ)| ^ (2 * angular) * ∫ radius in lower..1, radius *
            ‖iteratedDerivWithin radial (actualRadialValue lower positive bounded mode parameter source) (Icc lower 1) radius‖ ^ 2) ∧
      (∀ modes : Finset ℤ,
        (∑ mode ∈ modes, highRadialDerivativeEnergy lower positive bounded parameter source radial angular mode) ≤
          constant * ‖unitDiskCoreInto grade core‖ ^ 2) ∧
      Summable (highRadialDerivativeEnergy lower positive bounded parameter source radial angular) ∧
      (∑' mode : ℤ, highRadialDerivativeEnergy lower positive bounded parameter source radial angular mode) ≤
        constant * ‖unitDiskCoreInto grade core‖ ^ 2 := by
  obtain ⟨constant, nonnegative, bound⟩ := actualAllMixedRadial_finite grade lower positive bounded ceiling
  refine ⟨constant, nonnegative, ?_⟩
  intro parameter parameterBound source core same radial angular paid
  have finite := bound parameter parameterBound source core same radial angular paid
  exact ⟨highRadialDerivativeEnergy_literal lower positive bounded parameter source radial angular,
    finite, nonnegative_finite_total _ _
      (highRadialDerivativeEnergy_nonnegative lower positive bounded parameter source radial angular) finite⟩

end Grad.CircularHighRegularity
