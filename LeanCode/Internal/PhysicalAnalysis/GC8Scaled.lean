import GC8Envelope

noncomputable section

open Grad.PDEBootstrap

namespace Grad.GaugeCoefficients.Envelope

theorem scaledCellWeight_nonnegative (L ell : ℝ) (cell : ℤ) :
    0 ≤ scaledCellWeight L ell cell := Real.sqrt_nonneg _

theorem scaledCellWeight_add_le (L ell : ℝ) (first second : ℤ) :
    scaledCellWeight L ell (first + second) ≤
      Real.sqrt 2 * scaledCellWeight L ell first * scaledCellWeight L ell second := by
  let x : ℝ := (first : ℝ) * ell / L
  let y : ℝ := (second : ℝ) * ell / L
  have sumIdentity : ((first + second : ℤ) : ℝ) * ell / L = x + y := by
    dsimp [x, y]
    push_cast
    ring
  change Real.sqrt (1 + (((first + second : ℤ) : ℝ) * ell / L) ^ 2) ≤
    Real.sqrt 2 * Real.sqrt (1 + ((first : ℝ) * ell / L) ^ 2) *
      Real.sqrt (1 + ((second : ℝ) * ell / L) ^ 2)
  rw [sumIdentity]
  change Real.sqrt (1 + (x + y) ^ 2) ≤
    Real.sqrt 2 * Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2)
  have polynomialBound : 1 + (x + y) ^ 2 ≤ 2 * (1 + x ^ 2) * (1 + y ^ 2) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x * y)]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _))).mp
  rw [Real.sq_sqrt (by positivity : 0 ≤ 1 + (x + y) ^ 2), mul_pow, mul_pow,
    Real.sq_sqrt (by positivity : 0 ≤ (2 : ℝ)),
    Real.sq_sqrt (by positivity : 0 ≤ 1 + x ^ 2),
    Real.sq_sqrt (by positivity : 0 ≤ 1 + y ^ 2)]
  exact polynomialBound

theorem scaledTriangleGoal : ScaledTriangleGoal := by
  intro L sigma gamma ell _ first second
  exact scaledCellWeight_add_le L ell first second

theorem originalWidth_le_scaled (L ell : ℝ) (cell : ℤ)
    (positiveL : 0 < L) (ellNonnegative : 0 ≤ ell) (ellLeOne : ell ≤ 1) :
    ell * Grad.CellWeights.cellWeight cell ≤ max 1 L * scaledCellWeight L ell cell := by
  have LNonnegative : 0 ≤ L := positiveL.le
  have LNonzero : L ≠ 0 := positiveL.ne'
  have maximumNonnegative : 0 ≤ max 1 L := zero_le_one.trans (le_max_left 1 L)
  have ellLeMaximum : ell ≤ max 1 L := ellLeOne.trans (le_max_left 1 L)
  have LLeMaximum : L ≤ max 1 L := le_max_right 1 L
  have ellSquare : ell ^ 2 ≤ (max 1 L) ^ 2 :=
    (sq_le_sq₀ ellNonnegative maximumNonnegative).mpr ellLeMaximum
  have LSquare : L ^ 2 ≤ (max 1 L) ^ 2 :=
    (sq_le_sq₀ LNonnegative maximumNonnegative).mpr LLeMaximum
  let quotient : ℝ := (cell : ℝ) * ell / L
  have scaledSquare := mul_le_mul_of_nonneg_left LSquare (sq_nonneg quotient)
  have quotientIdentity : quotient ^ 2 * L ^ 2 = ((cell : ℝ) * ell) ^ 2 := by
    dsimp [quotient]
    field_simp
  apply (sq_le_sq₀
    (mul_nonneg ellNonnegative (Grad.CellWeights.cellWeight_pos cell).le)
    (mul_nonneg maximumNonnegative (scaledCellWeight_nonnegative L ell cell))).mp
  rw [mul_pow, Grad.CellBinomial.cellWeight_sq, mul_pow]
  unfold scaledCellWeight
  rw [Real.sq_sqrt (by positivity : 0 ≤ 1 + ((cell : ℝ) * ell / L) ^ 2)]
  dsimp [quotient] at scaledSquare quotientIdentity
  nlinarith [scaledSquare, quotientIdentity]

theorem scaledWidthGoal : ScaledWidthGoal := by
  intro L sigma gamma ell admissible cell
  exact originalWidth_le_scaled L ell cell admissible.1
    (admissible_ell_nonnegative admissible) (admissible_ell_le_one admissible)

end Grad.GaugeCoefficients.Envelope
