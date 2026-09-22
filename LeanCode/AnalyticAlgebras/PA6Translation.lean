import PA5PhaseConsumer
import FC3Core

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.PhaseAlgebra

open Grad.CartesianState

universe valueUniverse

variable {Value : Type valueUniverse} [NormedAddCommGroup Value]

/-- Translation of a square-summable sequence by a fixed shift. -/
def translateSequence (shift : ℤ)
    (field : lp (fun _ : ℤ => Value) 2) : lp (fun _ : ℤ => Value) 2 :=
  ⟨fun cell => field (cell - shift), by
    show Memℓp _ 2
    rw [memlp_iff_summable_sq]
    have base : Summable (fun cell : ℤ => ‖field cell‖ ^ 2) :=
      (memlp_iff_summable_sq _).mp (lp.memℓp field)
    exact ((Equiv.subRight shift).summable_iff
      (f := fun cell : ℤ => ‖field cell‖ ^ 2)).mpr base⟩

theorem translateSequence_apply (shift : ℤ)
    (field : lp (fun _ : ℤ => Value) 2) (cell : ℤ) :
    translateSequence shift field cell = field (cell - shift) := rfl

/-- Translation preserves the exponent-two norm. -/
theorem translateSequence_norm (shift : ℤ)
    (field : lp (fun _ : ℤ => Value) 2) :
    ‖translateSequence shift field‖ = ‖field‖ := by
  have translatedFormula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    (translateSequence shift field)
  have fieldFormula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at translatedFormula fieldFormula
  have squares : ‖translateSequence shift field‖ ^ 2 = ‖field‖ ^ 2 := by
    rw [translatedFormula, fieldFormula]
    calc (∑' cell : ℤ, ‖translateSequence shift field cell‖ ^ 2)
        = ∑' cell : ℤ, ‖field (cell - shift)‖ ^ 2 := rfl
      _ = ∑' cell : ℤ, ‖field cell‖ ^ 2 :=
          (Equiv.subRight shift).tsum_eq (fun cell : ℤ => ‖field cell‖ ^ 2)
  calc ‖translateSequence shift field‖
      = Real.sqrt (‖translateSequence shift field‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖field‖ ^ 2) := by rw [squares]
    _ = ‖field‖ := Real.sqrt_sq (norm_nonneg _)

theorem translateSequence_add (shift : ℤ)
    (first second : lp (fun _ : ℤ => Value) 2) :
    translateSequence shift (first + second) =
      translateSequence shift first + translateSequence shift second := by
  apply lp.ext
  funext cell
  rw [lp.coeFn_add, Pi.add_apply, translateSequence_apply, lp.coeFn_add,
    Pi.add_apply, translateSequence_apply, translateSequence_apply]

theorem translateSequence_smul [NormedSpace ℝ Value] (shift : ℤ) (scalar : ℝ)
    (field : lp (fun _ : ℤ => Value) 2) :
    translateSequence shift (scalar • field) =
      scalar • translateSequence shift field := by
  apply lp.ext
  funext cell
  rw [translateSequence_apply, lp.coeFn_smul, Pi.smul_apply, lp.coeFn_smul,
    Pi.smul_apply, translateSequence_apply]

end Grad.PhaseAlgebra
