import AKG28SameOriginalResponseRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped ENNReal BigOperators
namespace Grad.AnnularIncomingIntegrability
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.ClosedJets Grad.SourceCollarDivision Grad.AnnularLowEnergy Grad.AnnularVariational Grad.SourceBoundaryTrace

/-- The exact original low frequency controls the logarithmic density,
including the zero cell. No positive-cell assumption is used. -/
theorem lowMu_inverse_le_radius (length radius : ℝ) (cell : ℤ) (positive : 0 < radius) :
    (lowMu length radius cell)⁻¹ ≤ radius := by
  have bound := one_div_le_one_div_of_le (inv_pos.mpr positive) (lowMu_radial length radius cell positive)
  simpa only [one_div, inv_inv] using bound

/-- Exact Tonelli identity for the radial coordinate squares of an actual
countable Hilbert L2 field. This concerns integrals, not endpoint evaluation. -/
theorem radialLp_lintegral_sq (lower : ℝ) (field : CollarL2 (ComplexEuclidean 1) lower) :
    (∫⁻ radius, ENNReal.ofReal (‖field radius‖ ^ 2) ∂volume.restrict (Icc lower 1)) = ENNReal.ofReal (‖field‖ ^ 2) := by
  rw [radialLp_norm_sq]
  exact (ofReal_integral_eq_lintegral_ofReal (Lp.memLp field).norm.integrable_sq
    (Eventually.of_forall (fun _ => sq_nonneg _))).symm

theorem lp_summable_sq {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    (field : lp E 2) : Summable (fun index => ‖field index‖ ^ 2) := by
  have source := (memℓp_gen_iff (p := 2) (by norm_num)).mp (lp.memℓp field)
  simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using source

theorem lp_lintegral_tsum_sq {ι : Type*} [Countable ι] (lower : ℝ)
    (field : lp (fun _ : ι => CollarL2 (ComplexEuclidean 1) lower) 2) :
    (∫⁻ radius, ∑' index : ι, ENNReal.ofReal (‖field index radius‖ ^ 2) ∂volume.restrict (Icc lower 1)) =
      ENNReal.ofReal (‖field‖ ^ 2) := by
  rw [lintegral_tsum (fun index => (Lp.memLp (field index)).norm.integrable_sq.aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
  have normSum : ‖field‖ ^ 2 = ∑' index, ‖field index‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using (lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field)
  rw [normSum,ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (lp_summable_sq field)]
  exact tsum_congr (fun index => radialLp_lintegral_sq lower (field index))

end Grad.AnnularIncomingIntegrability
