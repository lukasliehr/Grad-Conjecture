import AKC1SameConjugatedKernelAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 250000
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients

/-- A single actual Fourier matrix entry, viewed as a bounded operator. -/
def fourierMatrixPoint {source target : ℕ} (output input : ℤ × ℤ) :
    (ComplexEuclidean source →L[ℂ] ComplexEuclidean target) →L[ℂ]
      (CellL2 source →L[ℂ] CellL2 target) :=
  ((ContinuousLinearMap.compL ℂ (CellL2 source) (ComplexEuclidean source) (CellL2 target)).flip
    (lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean source) 2 input)).comp
    ((ContinuousLinearMap.compL ℂ (ComplexEuclidean source) (ComplexEuclidean target) (CellL2 target))
      (lp.singleContinuousLinearMap ℂ (fun _ : ℤ × ℤ => ComplexEuclidean target) 2 output))

theorem fourierMatrixPoint_apply {source target : ℕ} (output input : ℤ × ℤ)
    (mapping : ComplexEuclidean source →L[ℂ] ComplexEuclidean target) (field : CellL2 source) :
    fourierMatrixPoint output input mapping field = lp.single 2 output (mapping (field input)) := rfl

theorem fourierMatrixPoint_bound {source target : ℕ} (output input : ℤ × ℤ)
    (mapping : ComplexEuclidean source →L[ℂ] ComplexEuclidean target) :
    ‖fourierMatrixPoint output input mapping‖ ≤ ‖mapping‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro field
  rw [fourierMatrixPoint_apply, lp.norm_single (by norm_num)]
  exact (mapping.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by norm_num) field input) (norm_nonneg _))

theorem fourierMatrixPoint_coordinate {source target : ℕ} (output input : ℤ × ℤ)
    (mapping : ComplexEuclidean source →L[ℂ] ComplexEuclidean target)
    (field : CellL2 source) (mode : ℤ × ℤ) :
    fourierMatrixPoint output input mapping field mode = if mode = output then mapping (field input) else 0 := by
  rw [fourierMatrixPoint_apply]
  simp only [lp.single_apply, Pi.single_apply]

end Grad.AnnularWeightedSmoothness
