import ASG25ExactWeakGraphCharacterization
import Mathlib.Analysis.Calculus.BumpFunction.Normed

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The literal distributional test class in AG2: compactly supported C∞
functions in the open collar, without an endpoint-test assumption. -/
def CompactWeakDerivative (dimension : ℕ) (lower : ℝ)
    (value derivative : CollarL2 (ComplexEuclidean dimension) lower) : Prop :=
  ∀ (test : ℝ → ℝ) (smooth : ContDiff ℝ ∞ test), HasCompactSupport test → tsupport test ⊆ Ioo lower 1 →
    ∀ vector : ComplexEuclidean dimension,
      collarPairing lower ⟨test, smooth.continuous⟩ vector derivative =
        -collarPairing lower ⟨deriv test, (contDiff_infty_iff_deriv.mp smooth).2.continuous⟩ vector value

theorem collarWeak_isCompact (dimension : ℕ) (lower : ℝ)
    (value derivative : CollarL2 (ComplexEuclidean dimension) lower)
    (weak : CollarWeakDerivative lower value derivative) : CompactWeakDerivative dimension lower value derivative := by
  intro test smooth _compact supported vector
  exact weak (collarCompactTest lower test smooth supported) vector

def interiorTestBump (lower : ℝ) (bounded : lower < 1) : ContDiffBump ((lower + 1) / 2) where
  rIn := (1 - lower) / 8
  rOut := (1 - lower) / 4
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

def normalizedInteriorTest (lower : ℝ) (bounded : lower < 1) : ℝ → ℝ :=
  (interiorTestBump lower bounded).normed volume

theorem normalizedInteriorTest_smooth (lower : ℝ) (bounded : lower < 1) :
    ContDiff ℝ ∞ (normalizedInteriorTest lower bounded) :=
  (interiorTestBump lower bounded).contDiff_normed

theorem normalizedInteriorTest_compact (lower : ℝ) (bounded : lower < 1) :
    HasCompactSupport (normalizedInteriorTest lower bounded) :=
  (interiorTestBump lower bounded).hasCompactSupport_normed

theorem normalizedInteriorTest_support (lower : ℝ) (bounded : lower < 1) :
    tsupport (normalizedInteriorTest lower bounded) ⊆ Ioo lower 1 := by
  rw [normalizedInteriorTest, ContDiffBump.tsupport_normed_eq]
  intro radius inside
  change dist radius ((lower + 1) / 2) ≤ (1 - lower) / 4 at inside
  rw [Real.dist_eq, abs_le] at inside
  constructor <;> linarith

theorem normalizedInteriorTest_integral (lower : ℝ) (bounded : lower < 1) :
    (∫ radius in lower..1, normalizedInteriorTest lower bounded radius) = 1 := by
  rw [intervalIntegral.integral_of_le bounded.le, ← integral_Icc_eq_integral_Ioc]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact (interiorTestBump lower bounded).integral_normed
  · intro radius outside
    apply image_eq_zero_of_notMem_tsupport
    intro member
    exact outside (Ioo_subset_Icc_self (normalizedInteriorTest_support lower bounded member))

end Grad.AnnularSourceGraph
