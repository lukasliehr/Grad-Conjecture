import AKF8FiniteOrderHomogeneousSmoothness
import AKH3ExactPhaseDiagonalCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
open scoped ContDiff
namespace Grad.AnnularWeightedSystem
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit
open Grad.AnnularSmoothCore Grad.PhaseAlgebra Grad.AnnularCurrentLow
open Grad.AnnularWeightedSmoothness Grad.AnnularKernelL2 Grad.AnnularVariational

/-- The literal original phase derivative on both field coordinates. -/
def phaseSlopePair (parameters : PhaseParameters) (reserve : ℕ) (radius : ℝ) :
    PhysicalHilbertPair →L[ℂ] PhysicalHilbertPair :=
  ((phaseSlopeDiagonal parameters 1 reserve radius).comp
    (ContinuousLinearMap.fst ℂ (CellL2 1) (CellL2 1))).prod
  ((phaseSlopeDiagonal parameters 1 reserve radius).comp
    (ContinuousLinearMap.snd ℂ (CellL2 1) (CellL2 1)))

theorem phaseSlopePair_smooth (parameters : PhaseParameters) (reserve order : ℕ)
    (enough : order + 5 ≤ reserve) (lower : ℝ) (bounded : lower < 1) :
    ContDiffOn ℝ order (phaseSlopePair parameters reserve) (Icc lower 1) := by
  have diagonal := phaseSlopeDiagonal_contDiffOn parameters 1 reserve order enough lower 1 bounded
  have first := finiteOrderOperatorComposition diagonal
    (show ContDiffOn ℝ order (fun _ : ℝ => ContinuousLinearMap.fst ℂ (CellL2 1) (CellL2 1)) (Icc lower 1) from contDiffOn_const)
  have second := finiteOrderOperatorComposition diagonal
    (show ContDiffOn ℝ order (fun _ : ℝ => ContinuousLinearMap.snd ℂ (CellL2 1) (CellL2 1)) (Icc lower 1) from contDiffOn_const)
  have combined := (finiteOrderOperatorComposition
    (show ContDiffOn ℝ order (fun _ : ℝ => ContinuousLinearMap.inl ℂ (CellL2 1) (CellL2 1)) (Icc lower 1) from contDiffOn_const)
    first).add (finiteOrderOperatorComposition
    (show ContDiffOn ℝ order (fun _ : ℝ => ContinuousLinearMap.inr ℂ (CellL2 1) (CellL2 1)) (Icc lower 1) from contDiffOn_const)
    second)
  apply combined.congr
  intro radius _
  apply ContinuousLinearMap.ext
  intro field
  apply Prod.ext <;> simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, Prod.fst_add, Prod.snd_add,
    add_zero, zero_add] <;> rfl

theorem phaseSlopePair_same (parameters : PhaseParameters) (reserve : ℕ) (enough : 5 ≤ reserve)
    (radius : ℝ) (higher lower : PhysicalHilbertPair)
    (same : ∀ mode, hilbertPairCoefficient mode higher =
      (Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ) ^ reserve •
        hilbertPairCoefficient mode lower) (mode : ℤ × ℤ) :
    hilbertPairCoefficient mode (phaseSlopePair parameters reserve radius higher) =
      annularPhaseSlope parameters mode.2 radius • hilbertPairCoefficient mode lower := by
  apply Prod.ext
  · exact phaseSlopeDiagonal_same parameters 1 reserve enough radius higher.1 lower.1
      (fun query => congrArg Prod.fst (same query)) mode
  · exact phaseSlopeDiagonal_same parameters 1 reserve enough radius higher.2 lower.2
      (fun query => congrArg Prod.snd (same query)) mode

end Grad.AnnularWeightedSystem
