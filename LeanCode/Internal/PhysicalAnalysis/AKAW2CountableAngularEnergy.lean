import AKAW1FullCellAngularEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.ActualNativeCellMoments
open Grad.ClosedJets Grad.SourceCollarCoefficients Grad.BoundaryTrace

/-- All integer cells are summed before the native bound is applied. -/
theorem fullCell_angular_energy {dimension : ℕ}
    (coefficients : CellL2 dimension) (field : ℤ → ℝ → ComplexEuclidean dimension)
    (continuousField : ∀ cell, Continuous (field cell))
    (coefficientBound : ∀ mode cell, ‖angularCoefficient (field cell) mode‖ ≤ ‖coefficients (mode,cell)‖) :
    (∫⁻ angle in Ioc (-Real.pi) Real.pi, ∑' cell : ℤ, ENNReal.ofReal (‖field cell angle‖ ^ 2)) ≤
      ENNReal.ofReal ((2 * Real.pi) * ‖coefficients‖ ^ 2) := by
  have measurable (cell : ℤ) : Measurable (fun angle => ENNReal.ofReal (‖field cell angle‖ ^ 2)) := by fun_prop
  rw [lintegral_tsum (fun cell => (measurable cell).aemeasurable)]
  apply ENNReal.summable.tsum_le_of_sum_le
  intro cells
  rw [← lintegral_finsetSum cells (fun cell _ => measurable cell)]
  have nonnegative : ∀ angle, 0 ≤ ∑ cell ∈ cells, ‖field cell angle‖ ^ 2 :=
    fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have continuous : Continuous (fun angle => ∑ cell ∈ cells, ‖field cell angle‖ ^ 2) := by fun_prop
  have integrable : IntegrableOn (fun angle => ∑ cell ∈ cells, ‖field cell angle‖ ^ 2) (Ioc (-Real.pi) Real.pi) :=
    continuous.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have realBound := finiteCell_angular_energy coefficients field continuousField coefficientBound cells
  rw [intervalIntegral.integral_of_le (neg_lt_self Real.pi_pos).le] at realBound
  calc
    _ = ∫⁻ angle in Ioc (-Real.pi) Real.pi, ENNReal.ofReal (∑ cell ∈ cells, ‖field cell angle‖ ^ 2) := by
      simp_rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    _ = ENNReal.ofReal (∫ angle in Ioc (-Real.pi) Real.pi, ∑ cell ∈ cells, ‖field cell angle‖ ^ 2) :=
      (ofReal_integral_eq_lintegral_ofReal integrable (Eventually.of_forall nonnegative)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal realBound

end Grad.ActualNativeCellMoments
