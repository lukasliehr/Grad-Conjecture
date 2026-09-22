import SCC22RadialCollection

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision

theorem cellL2_norm_sq {dimension : ℕ} (field : CellL2 dimension) :
    ‖field‖ ^ 2 = ∑' mode : ℤ × ℤ, ‖field mode‖ ^ 2 := by
  have equality := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at equality
  exact equality

theorem cellL2_square_summable {dimension : ℕ} (field : CellL2 dimension) :
    Summable (fun mode : ℤ × ℤ => ‖field mode‖ ^ 2) := by
  have member := lp.memℓp field
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)] at member
  simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using member

def separateRadialMode {dimension : ℕ} (lower : ℝ)
    (field : Lp (CellL2 dimension) 2 (volume.restrict (Set.Icc lower 1)))
    (mode : ℤ × ℤ) : RadialL2 dimension lower :=
  (lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode).compLp field

theorem separateRadialMode_ae {dimension : ℕ} (lower : ℝ)
    (field : Lp (CellL2 dimension) 2 (volume.restrict (Set.Icc lower 1))) (mode : ℤ × ℤ) :
    ∀ᵐ radius ∂volume.restrict (Set.Icc lower 1), separateRadialMode lower field mode radius = field radius mode :=
  (lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode).coeFn_compLp field

theorem separateRadialMode_memLp {dimension : ℕ} (lower : ℝ)
    (field : Lp (CellL2 dimension) 2 (volume.restrict (Set.Icc lower 1))) (mode : ℤ × ℤ) :
    MemLp (fun radius => field radius mode) 2 (volume.restrict (Set.Icc lower 1)) :=
  (lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode).comp_memLp field

theorem separateRadialMode_norm_sq {dimension : ℕ} (lower : ℝ)
    (field : Lp (CellL2 dimension) 2 (volume.restrict (Set.Icc lower 1))) (mode : ℤ × ℤ) :
    ‖separateRadialMode lower field mode‖ ^ 2 =
      ∫ radius, ‖field radius mode‖ ^ 2 ∂volume.restrict (Set.Icc lower 1) := by
  rw [radialLp_norm_sq]
  apply integral_congr_ae
  filter_upwards [separateRadialMode_ae lower field mode] with radius literal
  rw [literal]

theorem separateRadial_finite_bound {dimension : ℕ} (lower : ℝ)
    (field : Lp (CellL2 dimension) 2 (volume.restrict (Set.Icc lower 1)))
    (modes : Finset (ℤ × ℤ)) :
    ∑ mode ∈ modes, ‖separateRadialMode lower field mode‖ ^ 2 ≤ ‖field‖ ^ 2 := by
  simp_rw [separateRadialMode_norm_sq]
  rw [← integral_finsetSum modes
    (fun mode _ => (separateRadialMode_memLp lower field mode).norm.integrable_sq), cellL2_Lp_norm_sq]
  apply integral_mono_ae
    (integrable_finsetSum modes (fun mode _ => (separateRadialMode_memLp lower field mode).norm.integrable_sq))
    (Lp.memLp field).norm.integrable_sq
  filter_upwards with radius
  rw [cellL2_norm_sq]
  exact (cellL2_square_summable (field radius)).sum_le_tsum modes (fun mode _ => sq_nonneg _)

theorem separateRadial_memlp {dimension : ℕ} (lower : ℝ)
    (field : Lp (CellL2 dimension) 2 (volume.restrict (Set.Icc lower 1))) :
    Memℓp (separateRadialMode lower field) 2 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat]
  exact summable_of_sum_le (fun _ => sq_nonneg _) (separateRadial_finite_bound lower field)

def separateRadial {dimension : ℕ} (lower : ℝ)
    (field : Lp (CellL2 dimension) 2 (volume.restrict (Set.Icc lower 1))) : DivisionRow dimension lower :=
  ⟨separateRadialMode lower field, separateRadial_memlp lower field⟩

theorem separateRadial_ae {dimension : ℕ} (lower : ℝ)
    (field : Lp (CellL2 dimension) 2 (volume.restrict (Set.Icc lower 1))) :
    ∀ᵐ radius ∂volume.restrict (Set.Icc lower 1),
      ∀ mode : ℤ × ℤ, separateRadial lower field mode radius = field radius mode :=
  ae_all_iff.mpr (separateRadialMode_ae lower field)

theorem collect_separateRadial {dimension : ℕ} (lower : ℝ)
    (field : Lp (CellL2 dimension) 2 (volume.restrict (Set.Icc lower 1))) :
    collectRadial lower (separateRadial lower field) = field := by
  apply Lp.ext
  filter_upwards [collectRadial_ae lower (separateRadial lower field), separateRadial_ae lower field]
    with radius collected separated
  apply Subtype.ext
  funext mode
  exact (collected mode).trans (separated mode)

theorem separate_collectRadial {dimension : ℕ} (lower : ℝ) (field : DivisionRow dimension lower) :
    separateRadial lower (collectRadial lower field) = field := by
  apply Subtype.ext
  funext mode
  apply Lp.ext
  filter_upwards [separateRadial_ae lower (collectRadial lower field), collectRadial_ae lower field]
    with radius separated collected
  exact (separated mode).trans (collected mode)

theorem separateRadial_norm {dimension : ℕ} (lower : ℝ)
    (field : Lp (CellL2 dimension) 2 (volume.restrict (Set.Icc lower 1))) :
    ‖separateRadial lower field‖ = ‖field‖ := by
  rw [← collectRadial_norm lower (separateRadial lower field), collect_separateRadial]

end Grad.SourceCollarCoefficients
