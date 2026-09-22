import AJU1ClosedHilbertRadialJets
import AAZJ4TwoExtraGradeSummability

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter
open scoped ContDiff ENNReal
namespace Grad.AnnularPhysicalFourier
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularSmoothCore Grad.SourceCollarCoefficients

variable (lower : ℝ) (bounded : lower < 1) (curve : ℕ → ℝ → CellL2 1)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (curve grade) (Icc lower 1))
    (same : ∀ grade radius, radius ∈ Icc lower 1 → ∀ mode : ℤ × ℤ,
      curve grade radius mode =
        ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) • curve 0 radius mode)

def hilbertRadialJetCurve (order grade : ℕ) : C(Icc lower (1 : ℝ), CellL2 1) where
  toFun radius := iteratedDerivWithin order (curve grade) (Icc lower 1) radius.val
  continuous_toFun := continuousOn_iff_continuous_domRestrict.mp
    (radialJet_continuous lower bounded (curve grade) (smooth grade) order)

include same

/-- The fixed frequency grade commutes with the SAME physical radial jets.
No forward analytic phase factor is introduced. -/
theorem hilbertRadialJetSection_grade (order grade : ℕ) (mode : ℤ × ℤ) :
    hilbertRadialJetSection lower bounded curve smooth order grade mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        hilbertRadialJetSection lower bounded curve smooth order 0 mode := by
  apply ContinuousMap.ext
  intro radius
  let evaluate := lp.evalCLM ℝ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 mode
  change evaluate (iteratedDerivWithin order (curve grade) (Icc lower 1) radius.val) =
    ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
      evaluate (iteratedDerivWithin order (curve 0) (Icc lower 1) radius.val)
  rw [← radialJet_map lower bounded (curve grade) (smooth grade) evaluate order radius.val radius.property]
  have equality : EqOn (fun point => evaluate (curve grade point))
      (fun point => ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        evaluate (curve 0 point)) (Icc lower 1) := fun point inside => same grade point inside mode
  rw [iteratedDerivWithin_congr equality radius.property, iteratedDerivWithin_fun_const_smul_field]
  rw [radialJet_map lower bounded (curve 0) (smooth 0) evaluate order radius.val radius.property]

theorem hilbertRadialJetSection_weighted_bound (order grade : ℕ) (mode : ℤ × ℤ) :
    Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade *
      ‖hilbertRadialJetSection lower bounded curve smooth order 0 mode‖ ≤
      ‖hilbertRadialJetCurve lower bounded curve smooth order grade‖ := by
  have bound : ‖hilbertRadialJetSection lower bounded curve smooth order grade mode‖ ≤
      ‖hilbertRadialJetCurve lower bounded curve smooth order grade‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro radius
    exact (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
      (iteratedDerivWithin order (curve grade) (Icc lower 1) radius.val) mode).trans
      ((hilbertRadialJetCurve lower bounded curve smooth order grade).norm_coe_le_norm radius)
  rw [hilbertRadialJetSection_grade lower bounded curve smooth same order grade mode, norm_smul,
    Complex.norm_real, Real.norm_of_nonneg] at bound
  · exact bound
  · unfold Grad.AnnularVariational.annularFrequency
    positivity

/-- Uniform absolute convergence of every radial and tangential jet follows
from the compact norm of one higher Hilbert grade and the actual two-lattice
summability reserve. This concerns the full original mode set. -/
theorem hilbertRadialJetSection_weighted_summable (order grade : ℕ) :
    Summable (fun mode : ℤ × ℤ =>
      Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade *
        ‖hilbertRadialJetSection lower bounded curve smooth order 0 mode‖) := by
  let bound := ‖hilbertRadialJetCurve lower bounded curve smooth order (grade + 4)‖
  apply Summable.of_nonneg_of_le (fun mode => by
    exact mul_nonneg (pow_nonneg (by unfold Grad.AnnularVariational.annularFrequency; positivity) _) (norm_nonneg _))
    (fun mode => ?_) (Grad.AnnularJointRegularity.annularLattice_inverse_four_summable.mul_left bound)
  change Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade *
    ‖hilbertRadialJetSection lower bounded curve smooth order 0 mode‖ ≤
      bound * (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ 4)⁻¹
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by unfold Grad.AnnularVariational.annularFrequency; positivity)).mpr
  have higher := hilbertRadialJetSection_weighted_bound lower bounded curve smooth same order (grade + 4) mode
  calc
    _ = Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ (grade + 4) *
        ‖hilbertRadialJetSection lower bounded curve smooth order 0 mode‖ := by
      rw [pow_add]
      ring
    _ ≤ bound := higher

end Grad.AnnularPhysicalFourier
