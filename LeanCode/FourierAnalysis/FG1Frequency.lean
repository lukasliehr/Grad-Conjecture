import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space

noncomputable section

open scoped BigOperators ENNReal

namespace Grad.FourierGrade

/-- The literal product-torus Fourier index `κ = (k₁,k₂,n) ∈ ℤ³`. -/
abbrev FourierMode := ℤ × ℤ × ℤ

/-- The P10 frequency `( π k₁/2, π k₂/2, n )`. -/
def frequencyVector (mode : FourierMode) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(Real.pi / 2) * mode.1,
    (Real.pi / 2) * mode.2.1, mode.2.2]

/-- The literal inhomogeneous P10 Fourier weight. -/
def frequencyWeight (mode : FourierMode) : ℝ :=
  Real.sqrt (1 + ‖frequencyVector mode‖ ^ 2)

@[simp] theorem frequencyVector_zero (mode : FourierMode) :
    frequencyVector mode 0 = (Real.pi / 2) * mode.1 := rfl

@[simp] theorem frequencyVector_one (mode : FourierMode) :
    frequencyVector mode 1 = (Real.pi / 2) * mode.2.1 := rfl

@[simp] theorem frequencyVector_two (mode : FourierMode) :
    frequencyVector mode 2 = mode.2.2 := rfl

theorem frequencyWeight_one_le (mode : FourierMode) : 1 ≤ frequencyWeight mode := by
  exact Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg ‖frequencyVector mode‖])

theorem frequencyWeight_pos (mode : FourierMode) : 0 < frequencyWeight mode :=
  lt_of_lt_of_le zero_lt_one (frequencyWeight_one_le mode)

theorem frequencyWeight_ne_zero (mode : FourierMode) : frequencyWeight mode ≠ 0 :=
  ne_of_gt (frequencyWeight_pos mode)

theorem frequencyWeight_sq (mode : FourierMode) :
    frequencyWeight mode ^ 2 = 1 + ‖frequencyVector mode‖ ^ 2 := by
  exact Real.sq_sqrt (by positivity)

end Grad.FourierGrade
