import AKW1CofinalEnergyWithOneOuterTrace
import AKX1SameOriginalGraphCovariants

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators
namespace Grad.ActualPuncturedReconstruction
open Grad.ClosedJets Grad.SourceCollarDivision Grad.AnnularIncomingIntegrability Grad.AnnularRestriction
open Grad.PuncturedRetainedEnergy Grad.GaugeCoefficients.Physical.WeightedTrace Grad.SourceBoundaryTrace

/-- Actual vector bulk density in the original common weighted storage. -/
def physicalBulkSquare (dimension : ℕ) (lower : ℝ) (field : DivisionRow dimension lower) (radius : ℝ) : ℝ≥0∞ :=
  ∑' mode : ℤ × ℤ, ENNReal.ofReal (‖field mode radius‖ ^ 2)

theorem physicalBulkSquare_measurable (dimension : ℕ) (lower : ℝ) (field : DivisionRow dimension lower) :
    Measurable (physicalBulkSquare dimension lower field) :=
  Measurable.tsum (fun mode => (Lp.stronglyMeasurable (field mode)).measurable.norm.pow_const 2 |>.ennreal_ofReal)

theorem physicalBulkSquare_integral (dimension : ℕ) (lower : ℝ) (field : DivisionRow dimension lower) :
    (∫⁻ radius, physicalBulkSquare dimension lower field radius ∂volume.restrict (Icc lower 1)) =
      ENNReal.ofReal (‖field‖ ^ 2) := by
  change (∫⁻ radius, (∑' mode : ℤ × ℤ, ENNReal.ofReal (‖field mode radius‖ ^ 2)) ∂volume.restrict (Icc lower 1)) = _
  rw [lintegral_tsum (fun mode =>
    (Lp.memLp (field mode)).norm.integrable_sq.aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
  have normSum : ‖field‖ ^ 2 = ∑' mode, ‖field mode‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using (lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field)
  rw [normSum,ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (lp_summable_sq field)]
  apply tsum_congr
  intro mode
  rw [radialLp_norm_sq]
  exact (ofReal_integral_eq_lintegral_ofReal (Lp.memLp (field mode)).norm.integrable_sq
    (Eventually.of_forall (fun _ => sq_nonneg _))).symm

theorem physicalBulkSquare_restriction (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper)
    (field : DivisionRow dimension lower) :
    physicalBulkSquare dimension upper (originalBulkRestriction dimension lower upper included field) =ᵐ[volume.restrict (Icc upper 1)]
      physicalBulkSquare dimension lower field := by
  have rows : ∀ mode : ℤ × ℤ, ∀ᵐ radius ∂volume.restrict (Icc upper 1),
      originalBulkRestriction dimension lower upper included field mode radius = field mode radius :=
    fun mode => collarL2Restriction_ae dimension lower upper included (field mode)
  filter_upwards [ae_all_iff.mpr rows] with radius rows
  exact tsum_congr (fun mode => congrArg (fun value : ComplexEuclidean dimension => ENNReal.ofReal (‖value‖ ^ 2)) (rows mode))

end Grad.ActualPuncturedReconstruction
