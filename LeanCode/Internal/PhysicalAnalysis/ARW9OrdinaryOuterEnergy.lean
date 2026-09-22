import ARW8ActualRadialRowEnergy

noncomputable section
open Set MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualRadialWords
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.ActualOuterCollar Grad.ClosedDiskRegularity Grad.CollarCartesian Grad.BoundaryLift
open Grad.GaugeCoefficients.Algebra Grad.OrdinaryDiskCalculus
attribute [local instance] unitNormedSpace

theorem actualPolarRadialEnergy_mono (modes : Finset ℤ) (parameter : ℝ) (source : highDiskL2)
    (small large : ℕ) (upper : small ≤ large) :
    actualPolarRadialEnergy modes parameter source small ≤ actualPolarRadialEnergy modes parameter source large := by
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 * Real.pi)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    (fun order _ _ => actualPolarOrderEnergy_nonnegative modes parameter source order)

/-- Genuine ordinary Sobolev norm of the constructed finite outer field,
controlled by its actual mixed radial energies uniformly over finite supports. -/
theorem finiteOuterWithinOrdinary_radial_bound (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (modes : Finset ℤ) (parameter : ℝ) (source : highDiskL2)
      (core : ClosedJet 1) (same : source.val = closedL2Core core),
      ‖withinOrdinaryDisk grade (finiteOuterField modes parameter source)
        (finiteOuterField_smooth modes parameter source core same)‖ ^ 2 ≤
        constant * actualPolarRadialEnergy modes parameter source grade := by
  classical
  choose constants nonnegative bounds using
    (fun index : DerivativeIndex grade => actualOuterJet_radialEnergy_bound (derivativeMultiIndex index))
  refine ⟨∑ index, constants index, Finset.sum_nonneg (fun index _ => nonnegative index), ?_⟩
  intro modes parameter source core same
  rw [withinOrdinaryDisk_norm_sq, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro index _
  have energyBound := actualPolarRadialEnergy_mono modes parameter source
    (cartesianOrder (derivativeMultiIndex index)) grade index.property
  exact (bounds index modes parameter source core same).trans
    (mul_le_mul_of_nonneg_left energyBound (nonnegative index))

end Grad.ActualRadialWords
