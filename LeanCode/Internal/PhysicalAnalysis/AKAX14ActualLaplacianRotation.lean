import AKAX13ActualPrincipalWeakConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

open Set MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.RepresentedKernel.SpatialProduct

def startupWordLaplacian (test : Spatial → ℝ) (point : Spatial) : ℝ :=
  wordDerivative 2 (fun _ => 0) test point + wordDerivative 2 (fun _ => 1) test point

/-- The trace of the actual inverse rotation chain is the Cartesian Laplacian. -/
theorem startupWordLaplacian_rotation (angle : ℝ) (test : Spatial → ℝ) (point : Spatial) :
    startupWordLaplacian (fun source => test (planeRotationEquiv angle source)) point =
      startupWordLaplacian test (planeRotationEquiv angle point) := by
  unfold startupWordLaplacian
  rw [word_chain univ isOpen_univ (planeRotationEquiv angle) (fun _ => Iff.rfl) test 2 (fun _ => 0) point (mem_univ point),
    word_chain univ isOpen_univ (planeRotationEquiv angle) (fun _ => Iff.rfl) test 2 (fun _ => 1) point (mem_univ point),
    twisted_expansion, twisted_expansion, ← Finset.sum_add_distrib]
  simp_rw [← add_smul, rotation_two_chain_trace]
  have words : (Finset.univ : Finset (Word 2)) = {![0, 0], ![0, 1], ![1, 0], ![1, 1]} := by decide
  have firstWord : (![0, 0] : Word 2) = (fun _ => 0) := by
    funext position
    fin_cases position <;> rfl
  have secondWord : (![1, 1] : Word 2) = (fun _ => 1) := by
    funext position
    fin_cases position <;> rfl
  rw [words]
  simp
  rw [firstWord, secondWord]

theorem startupWordDerivative_const_mul (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test)
    (scalar : ℝ) (word : Word 2) (point : Spatial) :
    wordDerivative 2 word (fun source => scalar * test source) point =
      scalar * wordDerivative 2 word test point := by
  have derivative := iteratedFDeriv_const_smul_apply (x := point) (a := scalar)
    (smooth.contDiffAt.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
  exact congrArg (fun tensor => tensor (fun position => spatialDirection (word position))) derivative

end Grad.CartesianStartup
