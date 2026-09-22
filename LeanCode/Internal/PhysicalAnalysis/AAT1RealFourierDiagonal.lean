import AAG21ExactVariationalConsumer
import AFC1CellCutoff

noncomputable section
set_option maxHeartbeats 800000

namespace Grad.AnnularGrades

open Grad.AnnularVariational

section Diagonal
variable {Index E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def realDiagonalMode (coefficient : Index → ℝ) (index : Index) : E →L[ℂ] E :=
  (coefficient index : ℂ) • ContinuousLinearMap.id ℂ E

theorem realDiagonalMode_bound (coefficient : Index → ℝ) (constant : ℝ)
    (bounded : ∀ index, |coefficient index| ≤ constant) (index : Index) (value : E) :
    ‖realDiagonalMode coefficient index value‖ ≤ constant * ‖value‖ := by
  change ‖(coefficient index : ℂ) • value‖ ≤ _
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_right (bounded index) (norm_nonneg value)

/-- A genuine bounded scalar multiplier on the original Fourier sequence. -/
def realLpDiagonal (coefficient : Index → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ index, |coefficient index| ≤ constant) :
    lp (fun _ : Index => E) 2 →L[ℂ] lp (fun _ : Index => E) 2 :=
  complexLpTwoMap (realDiagonalMode coefficient) constant nonnegative
    (realDiagonalMode_bound coefficient constant bounded)

theorem realLpDiagonal_apply (coefficient : Index → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ index, |coefficient index| ≤ constant) (field : lp (fun _ : Index => E) 2) (index : Index) :
    realLpDiagonal coefficient constant nonnegative bounded field index = (coefficient index : ℂ) • field index := rfl

theorem realLpDiagonal_bound (coefficient : Index → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ index, |coefficient index| ≤ constant) (field : lp (fun _ : Index => E) 2) :
    ‖realLpDiagonal coefficient constant nonnegative bounded field‖ ≤ constant * ‖field‖ :=
  complexLpTwoMap_bound (realDiagonalMode coefficient) constant nonnegative
    (realDiagonalMode_bound coefficient constant bounded) field

theorem realLpDiagonal_injective (coefficient : Index → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ index, |coefficient index| ≤ constant) (nonzero : ∀ index, coefficient index ≠ 0) :
    Function.Injective (realLpDiagonal (E := E) coefficient constant nonnegative bounded) := by
  intro first second equality
  apply lp.ext
  funext index
  have point := congrArg (fun field : lp (fun _ : Index => E) 2 => field index) equality
  rw [realLpDiagonal_apply, realLpDiagonal_apply] at point
  exact (smul_right_injective E (show (coefficient index : ℂ) ≠ 0 by exact_mod_cast nonzero index)) point

end Diagonal

section Pairing
variable {Index E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem realLpDiagonal_adjoint (coefficient : Index → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ index, |coefficient index| ≤ constant) (first second : lp (fun _ : Index => E) 2) :
    inner ℂ (realLpDiagonal coefficient constant nonnegative bounded first) second =
      inner ℂ first (realLpDiagonal coefficient constant nonnegative bounded second) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro index
  simp only [realLpDiagonal_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal]

end Pairing

section Commutation
variable {Index E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem realLpDiagonal_commutes (coefficient : Index → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ index, |coefficient index| ≤ constant) (family : Index → E →L[ℂ] F)
    (familyConstant : ℝ) (familyNonnegative : 0 ≤ familyConstant)
    (familyBound : ∀ index value, ‖family index value‖ ≤ familyConstant * ‖value‖)
    (field : lp (fun _ : Index => E) 2) :
    realLpDiagonal coefficient constant nonnegative bounded
      (complexLpTwoMap family familyConstant familyNonnegative familyBound field) =
    complexLpTwoMap family familyConstant familyNonnegative familyBound
      (realLpDiagonal coefficient constant nonnegative bounded field) := by
  apply lp.ext
  funext index
  simp only [realLpDiagonal_apply, complexLpTwoMap_apply, map_smul]

end Commutation

end Grad.AnnularGrades
