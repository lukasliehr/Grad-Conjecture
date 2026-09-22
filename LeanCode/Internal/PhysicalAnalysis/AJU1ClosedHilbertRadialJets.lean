import AJI31SameSmoothSourceRHSConsumer
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter
open scoped ContDiff
namespace Grad.AnnularPhysicalFourier
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularSmoothCore Grad.SourceCollarCoefficients

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem radialJet_continuous (lower : ℝ) (bounded : lower < 1) (curve : ℝ → E)
    (smooth : ContDiffOn ℝ ∞ curve (Icc lower 1)) (order : ℕ) :
    ContinuousOn (iteratedDerivWithin order curve (Icc lower 1)) (Icc lower 1) :=
  smooth.continuousOn_iteratedDerivWithin
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl order) (uniqueDiffOn_Icc bounded)

theorem radialJet_derivative (lower : ℝ) (bounded : lower < 1) (curve : ℝ → E)
    (smooth : ContDiffOn ℝ ∞ curve (Icc lower 1)) (order : ℕ)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (iteratedDerivWithin order curve (Icc lower 1))
      (iteratedDerivWithin (order + 1) curve (Icc lower 1) radius) (Icc lower 1) radius := by
  rw [iteratedDerivWithin_succ]
  exact (smooth.differentiableOn_iteratedDerivWithin
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl order)
    (uniqueDiffOn_Icc bounded) radius inside).hasDerivWithinAt

/-- Constant real continuous linear observations commute with every actual
closed-collar radial derivative, including the endpoint derivatives. -/
theorem radialJet_map (lower : ℝ) (bounded : lower < 1) (curve : ℝ → E)
    (smooth : ContDiffOn ℝ ∞ curve (Icc lower 1)) (mapping : E →L[ℝ] F)
    (order : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    iteratedDerivWithin order (fun point => mapping (curve point)) (Icc lower 1) radius =
      mapping (iteratedDerivWithin order curve (Icc lower 1) radius) := by
  induction order generalizing radius with
  | zero => simp only [iteratedDerivWithin_zero]
  | succ order previous =>
      rw [iteratedDerivWithin_succ]
      rw [derivWithin_congr (fun point member => previous point member) (previous radius inside)]
      exact (mapping.hasFDerivAt.comp_hasDerivWithinAt radius
        (radialJet_derivative lower bounded curve smooth order radius inside)).derivWithin
          (uniqueDiffOn_Icc bounded radius inside)

variable (lower : ℝ) (bounded : lower < 1) (curve : ℕ → ℝ → CellL2 1)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (curve grade) (Icc lower 1))

/-- Every coordinate of every Hilbert radial jet has its canonical continuous
representative on the complete original closed interval. -/
def hilbertRadialJetSection (order grade : ℕ) (mode : ℤ × ℤ) : RadialContinuousSection 1 lower where
  toFun radius := iteratedDerivWithin order (curve grade) (Icc lower 1) radius.val mode
  continuous_toFun := continuousOn_iff_continuous_domRestrict.mp
    ((lp.evalCLM ℝ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 mode).continuous.comp_continuousOn
      (radialJet_continuous lower bounded (curve grade) (smooth grade) order))

theorem hilbertRadialJetSection_derivative (order grade : ℕ) (mode : ℤ × ℤ)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt
      (fun point => iteratedDerivWithin order (curve grade) (Icc lower 1) point mode)
      (hilbertRadialJetSection lower bounded curve smooth (order + 1) grade mode ⟨radius, inside⟩)
      (Icc lower 1) radius :=
  (lp.evalCLM ℝ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 mode).hasFDerivAt.comp_hasDerivWithinAt radius
    (radialJet_derivative lower bounded (curve grade) (smooth grade) order radius inside)

end Grad.AnnularPhysicalFourier
