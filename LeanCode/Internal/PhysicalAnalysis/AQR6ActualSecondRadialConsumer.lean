import AQR5CollectiveSecondRadial

noncomputable section
open Set MeasureTheory
open scoped BigOperators Interval
namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints

/-- The exact high-sector second derivative energy, with the five excluded
angular modes absent rather than assigned an unproved ODE. -/
def highSecondRadialEnergy (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1) (mode : ℤ) : ℝ :=
  if mode ∈ lowAngularModes then 0 else actualSecondRadialEnergy lower positive bounded parameter source core mode

theorem highSecondRadial_finite (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (source : unitDiskSobolev 0) (high : unitDiskBulk 0 source ∈ highDiskL2)
    (core : ClosedJet 1) (same : unitDiskBulk 0 source = closedL2Core core) (modes : Finset ℤ) :
    (∑ mode ∈ modes, highSecondRadialEnergy lower positive bounded parameter ⟨unitDiskBulk 0 source, high⟩ core mode) ≤
      secondRadialSourceConstant lower parameter * ‖source‖ ^ 2 := by
  have bound := actualSecondRadial_finite lower positive bounded parameter source high core same
    (modes.filter (fun mode => mode ∉ lowAngularModes)) (fun _ member => (Finset.mem_filter.mp member).2)
  simpa only [Finset.sum_filter, highSecondRadialEnergy, ite_not] using bound

private theorem nonnegative_bounded_total (energy : ℤ → ℝ) (constant : ℝ)
    (nonnegative : ∀ mode, 0 ≤ energy mode)
    (finite : ∀ modes : Finset ℤ, (∑ mode ∈ modes, energy mode) ≤ constant) :
    Summable energy ∧ (∑' mode : ℤ, energy mode) ≤ constant := by
  have summable := summable_of_sum_le nonnegative finite
  exact ⟨summable, summable.tsum_le_of_sum_le finite⟩

theorem highSecondRadialEnergy_nonnegative (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1) (mode : ℤ) :
    0 ≤ highSecondRadialEnergy lower positive bounded parameter source core mode := by
  change 0 ≤ if mode ∈ lowAngularModes then 0 else actualSecondRadialEnergy lower positive bounded parameter source core mode
  exact ite_nonneg (le_refl 0) (sq_nonneg _)

/-- Actual s=0 second-radial estimate for the original smooth high L2
source: r dr, the same continuous inverse coefficient, genuine derivatives
within both endpoints, and a constant independent of every angular cutoff. -/
theorem actualClosedCollarSecondDerivative (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (source : unitDiskSobolev 0) (high : unitDiskBulk 0 source ∈ highDiskL2)
    (core : ClosedJet 1) (same : unitDiskBulk 0 source = closedL2Core core) :
    (∀ mode : ℤ, mode ∉ lowAngularModes →
      highSecondRadialEnergy lower positive bounded parameter ⟨unitDiskBulk 0 source, high⟩ core mode =
        ∫ radius in lower..1, radius *
          ‖derivWithin (derivWithin (actualRadialValue lower positive bounded mode parameter ⟨unitDiskBulk 0 source, high⟩)
            (Icc lower 1)) (Icc lower 1) radius‖ ^ 2) ∧
    Summable (highSecondRadialEnergy lower positive bounded parameter ⟨unitDiskBulk 0 source, high⟩ core) ∧
    (∑' mode : ℤ, highSecondRadialEnergy lower positive bounded parameter ⟨unitDiskBulk 0 source, high⟩ core mode) ≤
      secondRadialSourceConstant lower parameter * ‖source‖ ^ 2 := by
  refine ⟨?_, nonnegative_bounded_total
    (highSecondRadialEnergy lower positive bounded parameter ⟨unitDiskBulk 0 source, high⟩ core)
    (secondRadialSourceConstant lower parameter * ‖source‖ ^ 2)
    (highSecondRadialEnergy_nonnegative lower positive bounded parameter ⟨unitDiskBulk 0 source, high⟩ core)
    (highSecondRadial_finite lower positive bounded parameter source high core same)⟩
  intro mode highMode
  have sameEnergy : highSecondRadialEnergy lower positive bounded parameter ⟨unitDiskBulk 0 source, high⟩ core mode =
      actualSecondRadialEnergy lower positive bounded parameter ⟨unitDiskBulk 0 source, high⟩ core mode := if_neg highMode
  exact sameEnergy.trans
    (actualSecondRadialEnergy_literal lower positive bounded parameter ⟨unitDiskBulk 0 source, high⟩ core same mode highMode)

/-- The three radial counts through total order two are collectively
square summable for the same actual inverse, using the original L2 source. -/
theorem actualClosedCollarThreeEnergies (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (source : unitDiskSobolev 0) (high : unitDiskBulk 0 source ∈ highDiskL2)
    (core : ClosedJet 1) (same : unitDiskBulk 0 source = closedL2Core core) :
    let energy := fun mode : ℤ => inverseZeroOneEnergy lower positive bounded.le parameter 0
      ⟨unitDiskBulk 0 source, high⟩ mode +
      highSecondRadialEnergy lower positive bounded parameter ⟨unitDiskBulk 0 source, high⟩ core mode;
    Summable energy ∧ (∑' mode : ℤ, energy mode) ≤
      (zeroOneCollarConstant 0 + secondRadialSourceConstant lower parameter) * ‖source‖ ^ 2 := by
  have first := actualCollectiveZeroOneCollar lower positive bounded.le parameter 0 source high
  have second := (actualClosedCollarSecondDerivative lower positive bounded parameter source high core same).2
  refine ⟨first.1.add second.1, ?_⟩
  dsimp only
  rw [first.1.tsum_add second.1]
  exact (add_le_add first.2 second.2).trans_eq (add_mul _ _ _).symm

end Grad.CircularHighRegularity
