import GC21FiniteCell

noncomputable section

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.WeightedTrace

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.BoundaryTrace

theorem apWeightedJet_boundary_coefficient {dimension : ℕ} (sigma gamma ell : ℝ)
    (cell mode : ℤ) (field : ClosedJet dimension) :
    fourierCoeff (fun angle : CellCircle =>
      (apWeightedJet sigma gamma ell cell field).value (boundaryDiskPoint angle)) mode =
      Real.exp (apBoundaryPhase sigma gamma ell cell) •
        fourierCoeff (fun angle : CellCircle => field.value (boundaryDiskPoint angle)) mode := by
  simp_rw [apWeightedJet_value, apWeight_boundary]
  exact fourierCoeff_real_smul _ _ _

def apBoundaryEnergy {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : ℤ →₀ ClosedJet dimension) (mode : ℤ × ℤ) : ℝ :=
  Real.exp (2 * apBoundaryPhase sigma gamma ell mode.2) * apBoundaryFrequency L ell mode ^ (2 * grade - 1) *
    ‖apCoreBoundaryCoefficient field mode‖ ^ 2

theorem apBoundaryEnergy_nonnegative {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : ℤ →₀ ClosedJet dimension) (mode : ℤ × ℤ) : 0 ≤ apBoundaryEnergy L sigma gamma ell grade field mode :=
  mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg (apBoundaryFrequency_pos L ell _).le _)) (sq_nonneg _)

theorem apFiniteBoundaryCell {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (field : ℤ →₀ ClosedJet dimension) (cell : ℤ) (modes : Finset ℤ) :
    (∑ mode ∈ modes, apBoundaryEnergy L sigma gamma ell grade field (mode, cell)) ≤
      traceCellConstant grade * ‖apRowLinear (grade := grade) L sigma gamma ell cell (field cell)‖ ^ 2 := by
  have bound := apFiniteCellTrace L sigma gamma ell cell grade gradePositive (field cell) modes
  apply le_trans (le_of_eq ?_) bound
  apply Finset.sum_congr rfl
  intro mode _
  rw [apWeightedJet_boundary_coefficient, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_pow]
  unfold apBoundaryEnergy apCoreBoundaryCoefficient
  simp only [two_mul, Real.exp_add, pow_two]
  ring

theorem apFiniteRows_summable {dimension grade : ℕ} (L sigma gamma ell : ℝ)
    (field : ℤ →₀ ClosedJet dimension) :
    Summable (fun cell : ℤ => ‖apRowLinear (grade := grade) L sigma gamma ell cell (field cell)‖ ^ 2) := by
  have summable := (memlp_iff_summable_sq _).mp (apFiniteEmbed (grade := grade) L sigma gamma ell field).property
  simpa only [apFiniteEmbed_apply] using summable

theorem apFinite_norm_sq_rows {dimension grade : ℕ} (L sigma gamma ell : ℝ)
    (field : ℤ →₀ ClosedJet dimension) :
    ‖apFiniteInto (grade := grade) L sigma gamma ell field‖ ^ 2 =
      ∑' cell : ℤ, ‖apRowLinear (grade := grade) L sigma gamma ell cell (field cell)‖ ^ 2 := by
  change ‖apFiniteEmbed (grade := grade) L sigma gamma ell field‖ ^ 2 = _
  have identity := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    (apFiniteEmbed (grade := grade) L sigma gamma ell field)
  norm_num at identity
  simpa only [apFiniteEmbed_apply] using identity

theorem apFiniteBoundaryBound {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (field : ℤ →₀ ClosedJet dimension) (modes : Finset (ℤ × ℤ)) :
    (∑ mode ∈ modes, apBoundaryEnergy L sigma gamma ell grade field mode) ≤
      traceCellConstant grade * ‖apFiniteInto (grade := grade) L sigma gamma ell field‖ ^ 2 := by
  classical
  have rectangular : modes ⊆ modes.image Prod.fst ×ˢ modes.image Prod.snd := by
    intro mode member
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨mode, member, rfl⟩,
      Finset.mem_image.mpr ⟨mode, member, rfl⟩⟩
  calc
    _ ≤ ∑ mode ∈ modes.image Prod.fst ×ˢ modes.image Prod.snd,
        apBoundaryEnergy L sigma gamma ell grade field mode :=
      Finset.sum_le_sum_of_subset_of_nonneg rectangular
        (fun mode _ _ => apBoundaryEnergy_nonnegative L sigma gamma ell grade field mode)
    _ = ∑ cell ∈ modes.image Prod.snd, ∑ mode ∈ modes.image Prod.fst,
        apBoundaryEnergy L sigma gamma ell grade field (mode, cell) := by
      rw [Finset.sum_product, Finset.sum_comm]
    _ ≤ ∑ cell ∈ modes.image Prod.snd,
        traceCellConstant grade * ‖apRowLinear (grade := grade) L sigma gamma ell cell (field cell)‖ ^ 2 :=
      Finset.sum_le_sum (fun cell _ => apFiniteBoundaryCell L sigma gamma ell grade gradePositive field cell _)
    _ = traceCellConstant grade * (∑ cell ∈ modes.image Prod.snd,
        ‖apRowLinear (grade := grade) L sigma gamma ell cell (field cell)‖ ^ 2) := by rw [Finset.mul_sum]
    _ ≤ traceCellConstant grade * (∑' cell : ℤ,
        ‖apRowLinear (grade := grade) L sigma gamma ell cell (field cell)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        ((apFiniteRows_summable L sigma gamma ell field).sum_le_tsum _ (fun _ _ => sq_nonneg _))
        (traceCellConstant_nonnegative grade)
    _ = _ := by rw [apFinite_norm_sq_rows]

theorem apBoundary_summable {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (field : ℤ →₀ ClosedJet dimension) :
    Summable (apBoundaryEnergy L sigma gamma ell grade field) :=
  summable_of_sum_le (apBoundaryEnergy_nonnegative L sigma gamma ell grade field)
    (apFiniteBoundaryBound L sigma gamma ell grade gradePositive field)

theorem apBoundary_bound {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (field : ℤ →₀ ClosedJet dimension) :
    (∑' mode : ℤ × ℤ, apBoundaryEnergy L sigma gamma ell grade field mode) ≤
      traceCellConstant grade * ‖apFiniteInto (grade := grade) L sigma gamma ell field‖ ^ 2 :=
  Real.tsum_le_of_sum_le (apBoundaryEnergy_nonnegative L sigma gamma ell grade field)
    (apFiniteBoundaryBound L sigma gamma ell grade gradePositive field)

end Grad.GaugeCoefficients.Physical.WeightedTrace
