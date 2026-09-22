import GC18APKernel
import ProductSequenceConvolution

noncomputable section

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.NonlinearProduct

section Shift

variable {First Second : Type} [NormedAddCommGroup First] [NormedSpace ℂ First]
    [NormedAddCommGroup Second] [NormedSpace ℂ Second]
    (shift : ℤ) (kernel : ℤ → First →L[ℂ] Second) (bound : ℝ) (nonnegative : 0 ≤ bound)
    (bounded : ∀ cell, ‖kernel cell‖ ≤ bound)

def apShiftValue (field : lp (fun _ : ℤ => First) 2) : lp (fun _ : ℤ => Second) 2 :=
  ⟨fun cell => kernel cell (field (cell - shift)), by
    let comparison := (bound : ℂ) • shiftLp field shift
    apply (lp.memℓp comparison).mono'
    intro cell
    change ‖kernel cell (field (cell - shift))‖ ≤ ‖(bound : ℂ) • field (cell - shift)‖
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg nonnegative]
    exact ((kernel cell).le_opNorm _).trans (mul_le_mul_of_nonneg_right (bounded cell) (norm_nonneg _))⟩

theorem apShiftValue_norm_le (field : lp (fun _ : ℤ => First) 2) :
    ‖apShiftValue shift kernel bound nonnegative bounded field‖ ≤ bound * ‖field‖ := by
  calc
    _ ≤ ‖(bound : ℂ) • shiftLp field shift‖ := by
      apply lp.norm_mono (by norm_num)
      intro cell
      change ‖kernel cell (field (cell - shift))‖ ≤ ‖(bound : ℂ) • field (cell - shift)‖
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg nonnegative]
      exact ((kernel cell).le_opNorm _).trans (mul_le_mul_of_nonneg_right (bounded cell) (norm_nonneg _))
    _ = _ := by rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg nonnegative, shiftLp_norm]

def apShiftLinear : lp (fun _ : ℤ => First) 2 →ₗ[ℂ] lp (fun _ : ℤ => Second) 2 where
  toFun := apShiftValue shift kernel bound nonnegative bounded
  map_add' first second := by
    apply lp.ext
    funext cell
    exact (kernel cell).map_add (first (cell - shift)) (second (cell - shift))
  map_smul' scalar field := by
    apply lp.ext
    funext cell
    exact (kernel cell).map_smul scalar (field (cell - shift))

def apShiftOperator : lp (fun _ : ℤ => First) 2 →L[ℂ] lp (fun _ : ℤ => Second) 2 :=
  (apShiftLinear shift kernel bound nonnegative bounded).mkContinuous bound
    (apShiftValue_norm_le shift kernel bound nonnegative bounded)

theorem apShiftOperator_apply (field : lp (fun _ : ℤ => First) 2) (cell : ℤ) :
    apShiftOperator shift kernel bound nonnegative bounded field cell = kernel cell (field (cell - shift)) := rfl

theorem apShiftOperator_norm_le : ‖apShiftOperator shift kernel bound nonnegative bounded‖ ≤ bound :=
  (apShiftLinear shift kernel bound nonnegative bounded).mkContinuous_norm_le nonnegative
    (apShiftValue_norm_le shift kernel bound nonnegative bounded)

end Shift

end Grad.GaugeCoefficients.Physical.RadialLedger
