import AQS2WeightedSecondRadial

noncomputable section
open Set MeasureTheory
open scoped BigOperators Interval
namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints

/-- Actual weighted second-radial energy with the five removed modes absent. -/
def highWeightedSecondRadialEnergy (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (order : ℕ) (source : highDiskL2) (core : ClosedJet 1) (mode : ℤ) : ℝ :=
  |(mode : ℝ)| ^ (2 * order) * highSecondRadialEnergy lower positive bounded parameter source core mode

theorem highWeightedSecondRadial_nonnegative (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (order : ℕ) (source : highDiskL2) (core : ClosedJet 1) (mode : ℤ) :
    0 ≤ highWeightedSecondRadialEnergy lower positive bounded parameter order source core mode :=
  mul_nonneg (pow_nonneg (abs_nonneg _) _)
    (highSecondRadialEnergy_nonnegative lower positive bounded parameter source core mode)

theorem highWeightedSecondRadial_finite (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (order : ℕ) (source : unitDiskSobolev order)
    (high : unitDiskBulk order source ∈ highDiskL2) (core : ClosedJet 1)
    (same : unitDiskBulk order source = closedL2Core core) (modes : Finset ℤ) :
    (∑ mode ∈ modes, highWeightedSecondRadialEnergy lower positive bounded parameter order
      ⟨unitDiskBulk order source, high⟩ core mode) ≤ weightedSecondRadialConstant lower parameter order * ‖source‖ ^ 2 := by
  have bound := actualSecondRadial_weighted_finite lower positive bounded parameter order source high core same
    (modes.filter (fun mode => mode ∉ lowAngularModes)) (fun _ member => (Finset.mem_filter.mp member).2)
  simpa only [Finset.sum_filter, highWeightedSecondRadialEnergy, highSecondRadialEnergy,
    mul_ite, mul_zero, ite_not] using bound

private theorem weighted_nonnegative_bounded_total (energy : ℤ → ℝ) (constant : ℝ)
    (nonnegative : ∀ mode, 0 ≤ energy mode)
    (finite : ∀ modes : Finset ℤ, (∑ mode ∈ modes, energy mode) ≤ constant) :
    Summable energy ∧ (∑' mode : ℤ, energy mode) ≤ constant := by
  have summable := summable_of_sum_le nonnegative finite
  exact ⟨summable, summable.tsum_le_of_sum_le finite⟩

/-- For the same actual weak inverse and original smooth Hs source, every
weighted second-radial coefficient is literal and collectively summable.
The squared constant has at most k^4 dependence, uniformly in angular cutoff. -/
theorem actualClosedCollarWeightedSecondDerivative (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (order : ℕ) (source : unitDiskSobolev order)
    (high : unitDiskBulk order source ∈ highDiskL2) (core : ClosedJet 1)
    (same : unitDiskBulk order source = closedL2Core core) :
    (∀ mode : ℤ, mode ∉ lowAngularModes →
      highWeightedSecondRadialEnergy lower positive bounded parameter order ⟨unitDiskBulk order source, high⟩ core mode =
        |(mode : ℝ)| ^ (2 * order) * ∫ radius in lower..1, radius *
          ‖derivWithin (derivWithin (actualRadialValue lower positive bounded mode parameter ⟨unitDiskBulk order source, high⟩)
            (Icc lower 1)) (Icc lower 1) radius‖ ^ 2) ∧
    Summable (highWeightedSecondRadialEnergy lower positive bounded parameter order ⟨unitDiskBulk order source, high⟩ core) ∧
    (∑' mode : ℤ, highWeightedSecondRadialEnergy lower positive bounded parameter order ⟨unitDiskBulk order source, high⟩ core mode) ≤
      weightedSecondRadialConstant lower parameter order * ‖source‖ ^ 2 := by
  refine ⟨?_, weighted_nonnegative_bounded_total
    (highWeightedSecondRadialEnergy lower positive bounded parameter order ⟨unitDiskBulk order source, high⟩ core)
    (weightedSecondRadialConstant lower parameter order * ‖source‖ ^ 2)
    (highWeightedSecondRadial_nonnegative lower positive bounded parameter order ⟨unitDiskBulk order source, high⟩ core)
    (highWeightedSecondRadial_finite lower positive bounded parameter order source high core same)⟩
  intro mode highMode
  have sameEnergy : highSecondRadialEnergy lower positive bounded parameter ⟨unitDiskBulk order source, high⟩ core mode =
      actualSecondRadialEnergy lower positive bounded parameter ⟨unitDiskBulk order source, high⟩ core mode := if_neg highMode
  exact congrArg (fun energy : ℝ => |(mode : ℝ)| ^ (2 * order) * energy)
    (sameEnergy.trans (actualSecondRadialEnergy_literal lower positive bounded parameter
      ⟨unitDiskBulk order source, high⟩ core same mode highMode))

/-- All source grades: the three mixed radial counts through count two
at total order s+2 are summable for one and the same actual inverse. -/
theorem actualClosedCollarWeightedThreeEnergies (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (order : ℕ) (source : unitDiskSobolev order)
    (high : unitDiskBulk order source ∈ highDiskL2) (core : ClosedJet 1)
    (same : unitDiskBulk order source = closedL2Core core) :
    let energy := fun mode : ℤ => inverseZeroOneEnergy lower positive bounded.le parameter order
      ⟨unitDiskBulk order source, high⟩ mode +
      highWeightedSecondRadialEnergy lower positive bounded parameter order ⟨unitDiskBulk order source, high⟩ core mode;
    Summable energy ∧ (∑' mode : ℤ, energy mode) ≤
      (zeroOneCollarConstant order + weightedSecondRadialConstant lower parameter order) * ‖source‖ ^ 2 := by
  have first := actualCollectiveZeroOneCollar lower positive bounded.le parameter order source high
  have second := (actualClosedCollarWeightedSecondDerivative lower positive bounded parameter order source high core same).2
  refine ⟨first.1.add second.1, ?_⟩
  dsimp only
  rw [first.1.tsum_add second.1]
  exact (add_le_add first.2 second.2).trans_eq (add_mul _ _ _).symm

end Grad.CircularHighRegularity
