import SCC20ActualKappaRealization
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.SourceCollarDivision

variable {Index Point : Type*} [Countable Index] [MeasurableSpace Point]

/-- Positive Fubini in real coordinates, including the almost-everywhere
summability needed for the actual full-cell radial representative. -/
theorem positive_series_integrable (measure : Measure Point)
    (value : Index → Point → ℝ) (nonnegative : ∀ index point, 0 ≤ value index point)
    (integrable : ∀ index, Integrable (value index) measure)
    (summable : Summable (fun index => ∫ point, value index point ∂measure)) :
    (∀ᵐ point ∂measure, Summable (fun index => value index point)) ∧
      Integrable (fun point => ∑' index, value index point) measure := by
  let entry (index : Index) : Lp ℝ 1 measure := (integrable index).toL1 (value index)
  have entryNorm (index : Index) : ‖entry index‖ = ∫ point, value index point ∂measure := by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [(integrable index).coeFn_toL1] with point literal
    rw [literal, Real.norm_of_nonneg (nonnegative index point)]
  have entrySummable : Summable (fun index => ‖entry index‖) := by
    simpa only [entryNorm] using summable
  have pointSeries := Lp.hasSum_coeFn_tsum
    (tsum_enorm_ne_top_iff_summable_norm.mpr entrySummable)
  have representatives : ∀ᵐ point ∂measure, ∀ index, entry index point = value index point :=
    ae_all_iff.mpr (fun index => (integrable index).coeFn_toL1)
  have literal : ∀ᵐ point ∂measure,
      HasSum (fun index => value index point) ((∑' index, entry index) point) := by
    filter_upwards [pointSeries, representatives] with point series equalities
    exact series.congr_fun (fun index => (equalities index).symm)
  refine ⟨literal.mono (fun _ series => series.summable), ?_⟩
  exact (memLp_one_iff_integrable.mp (Lp.memLp (∑' index, entry index))).congr
    (literal.mono (fun _ series => series.tsum_eq.symm))

theorem radialRow_square_summable {dimension : ℕ} (lower : ℝ)
    (field : DivisionRow dimension lower) : Summable (fun mode => ‖field mode‖ ^ 2) := by
  have member := lp.memℓp field
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)] at member
  simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using member

theorem radialRow_norm_sq {dimension : ℕ} (lower : ℝ)
    (field : DivisionRow dimension lower) : ‖field‖ ^ 2 = ∑' mode, ‖field mode‖ ^ 2 := by
  have equality := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at equality
  exact equality

def radialRowSquare {dimension : ℕ} (lower : ℝ)
    (field : DivisionRow dimension lower) (radius : ℝ) : ℝ :=
  ∑' mode : ℤ × ℤ, ‖field mode radius‖ ^ 2

theorem radialRowSquare_properties {dimension : ℕ} (lower : ℝ)
    (field : DivisionRow dimension lower) :
    (∀ᵐ radius ∂volume.restrict (Set.Icc lower 1),
      Summable (fun mode : ℤ × ℤ => ‖field mode radius‖ ^ 2)) ∧
    Integrable (radialRowSquare lower field) (volume.restrict (Set.Icc lower 1)) := by
  apply positive_series_integrable _ _ (fun _ _ => sq_nonneg _)
    (fun mode => (Lp.memLp (field mode)).norm.integrable_sq)
  simpa only [← radialLp_norm_sq] using radialRow_square_summable lower field

theorem radialRowSquare_integral {dimension : ℕ} (lower : ℝ)
    (field : DivisionRow dimension lower) :
    ∫ radius, radialRowSquare lower field radius ∂volume.restrict (Set.Icc lower 1) = ‖field‖ ^ 2 := by
  rw [radialRow_norm_sq]
  have interchange := integral_tsum_of_summable_integral_norm
    (fun mode : ℤ × ℤ => (Lp.memLp (field mode)).norm.integrable_sq)
    (show Summable (fun mode : ℤ × ℤ =>
      ∫ radius, ‖‖field mode radius‖ ^ 2‖ ∂volume.restrict (Set.Icc lower 1)) by
        simp only [Real.norm_of_nonneg (sq_nonneg _), ← radialLp_norm_sq]
        exact radialRow_square_summable lower field)
  simpa only [← radialLp_norm_sq, radialRowSquare] using interchange.symm

end Grad.SourceCollarCoefficients
