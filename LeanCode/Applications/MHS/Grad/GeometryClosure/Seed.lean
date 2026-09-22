import Grad.GeometryClosure.Harmonic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace

/-! G01 and the matrix portion of G20. These are coordinate matrices, with no norm claims. -/
noncomputable section
namespace Grad.GeometryClosure
open Matrix

/-- Rotation in the ordered real plane. -/
def planarRotation (alpha : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos alpha, -Real.sin alpha; Real.sin alpha, Real.cos alpha]

/-- Rotation of a real diagonal matrix. -/
def rotatedDiagonal (x y alpha : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  planarRotation alpha * !![x, 0; 0, y] * (planarRotation alpha)ᵀ

/-- The positive diagonal seed, with its angle passed directly. -/
def seedMatrix (rho alpha : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  rotatedDiagonal (Real.sqrt (1 + rho)) (Real.sqrt (1 - rho)) alpha

/-- Explicit inverse candidate; its inverse laws require -1 < rho < 1. -/
def seedInverse (rho alpha : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  rotatedDiagonal (Real.sqrt (1 + rho))⁻¹ (Real.sqrt (1 - rho))⁻¹ alpha

/-- The harmonic seed in D03, with scalar parameters unbundled. -/
def harmonicSeedMatrix (rho alpha0 delta lambda t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  seedMatrix rho (seedAngle alpha0 delta lambda t)

/-- The explicit normalized shape entries (31), defined for every real rho. -/
def angleShape (rho alpha : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 + rho * Real.cos (2 * alpha)) / 2, rho * Real.sin (2 * alpha) / 2;
     rho * Real.sin (2 * alpha) / 2, (1 - rho * Real.cos (2 * alpha)) / 2]

/-- The normal-frame reflection matrix. -/
def normalReflection (chi : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, chi]

theorem planarRotation_transpose (alpha : ℝ) :
    (planarRotation alpha)ᵀ = planarRotation (-alpha) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planarRotation, Real.cos_neg, Real.sin_neg]

theorem planarRotation_mul_transpose (alpha : ℝ) :
    planarRotation alpha * (planarRotation alpha)ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planarRotation, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith [Real.sin_sq_add_cos_sq alpha]

theorem planarRotation_transpose_mul (alpha : ℝ) :
    (planarRotation alpha)ᵀ * planarRotation alpha = 1 := by
  simpa [planarRotation_transpose] using planarRotation_mul_transpose (-alpha)

theorem planarRotation_det (alpha : ℝ) : (planarRotation alpha).det = 1 := by
  simp [planarRotation, Matrix.det_fin_two]
  nlinarith [Real.sin_sq_add_cos_sq alpha]

theorem planarRotation_add (alpha beta : ℝ) :
    planarRotation (alpha + beta) = planarRotation alpha * planarRotation beta := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planarRotation, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

theorem rotatedDiagonal_entries (x y alpha : ℝ) :
    rotatedDiagonal x y alpha =
      !![x * Real.cos alpha ^ 2 + y * Real.sin alpha ^ 2,
        (x - y) * Real.cos alpha * Real.sin alpha;
        (x - y) * Real.cos alpha * Real.sin alpha,
        x * Real.sin alpha ^ 2 + y * Real.cos alpha ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotatedDiagonal, planarRotation, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem rotatedDiagonal_transpose (x y alpha : ℝ) :
    (rotatedDiagonal x y alpha)ᵀ = rotatedDiagonal x y alpha := by
  rw [rotatedDiagonal_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem rotatedDiagonal_one (alpha : ℝ) : rotatedDiagonal 1 1 alpha = 1 := by
  have hd : (!![(1 : ℝ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  simp [rotatedDiagonal, hd, planarRotation_mul_transpose]

theorem rotatedDiagonal_mul (x y u v alpha : ℝ) :
    rotatedDiagonal x y alpha * rotatedDiagonal u v alpha =
      rotatedDiagonal (x * u) (y * v) alpha := by
  have hd : (!![x, 0; 0, y] : Matrix (Fin 2) (Fin 2) ℝ) * !![u, 0; 0, v] =
      !![x * u, 0; 0, y * v] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  unfold rotatedDiagonal
  calc
    _ = planarRotation alpha * (!![x, 0; 0, y] *
      ((planarRotation alpha)ᵀ * planarRotation alpha) * !![u, 0; 0, v]) *
        (planarRotation alpha)ᵀ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [planarRotation_transpose_mul, Matrix.mul_one, hd]

theorem rotatedDiagonal_trace (x y alpha : ℝ) :
    (rotatedDiagonal x y alpha).trace = x + y := by
  rw [rotatedDiagonal_entries]
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  linear_combination (x + y) * Real.sin_sq_add_cos_sq alpha

theorem rotatedDiagonal_det (x y alpha : ℝ) :
    (rotatedDiagonal x y alpha).det = x * y := by
  simp only [rotatedDiagonal, Matrix.det_mul, Matrix.det_transpose, planarRotation_det, one_mul, mul_one]
  simp [Matrix.det_fin_two]

/-- Exact equivalence with the rotation-conjugate seed formula in D03. -/
theorem harmonicSeedMatrix_formula (rho alpha0 delta lambda t : ℝ) :
    harmonicSeedMatrix rho alpha0 delta lambda t =
      planarRotation (seedAngle alpha0 delta lambda t) *
      !![Real.sqrt (1 + rho), 0; 0, Real.sqrt (1 - rho)] *
      planarRotation (-seedAngle alpha0 delta lambda t) := by
  simp [harmonicSeedMatrix, seedMatrix, rotatedDiagonal, planarRotation_transpose]

theorem seed_diagonal_positive {rho : ℝ} (hrl : -1 < rho) (hru : rho < 1) :
    0 < Real.sqrt (1 + rho) ∧ 0 < Real.sqrt (1 - rho) := by
  constructor <;> apply Real.sqrt_pos.mpr <;> linarith

/-- G01: both products with the explicitly defined inverse. -/
theorem seed_inverse_identities {rho : ℝ} (hrl : -1 < rho) (hru : rho < 1) (alpha : ℝ) :
    seedInverse rho alpha * seedMatrix rho alpha = 1 ∧
    seedMatrix rho alpha * seedInverse rho alpha = 1 := by
  obtain ⟨hp, hm⟩ := seed_diagonal_positive hrl hru
  constructor <;>
    simp [seedInverse, seedMatrix, rotatedDiagonal_mul, ne_of_gt hp, ne_of_gt hm,
      rotatedDiagonal_one]

theorem seedInverse_eq_inv {rho : ℝ} (hrl : -1 < rho) (hru : rho < 1) (alpha : ℝ) :
    seedInverse rho alpha = (seedMatrix rho alpha)⁻¹ := by
  exact (Matrix.inv_eq_left_inv (seed_inverse_identities hrl hru alpha).1).symm

/-- G01: the full MMᵀ matrix, before normalization. -/
theorem seed_mul_transpose {rho : ℝ} (hrl : -1 < rho) (hru : rho < 1) (alpha : ℝ) :
    seedMatrix rho alpha * (seedMatrix rho alpha)ᵀ = rotatedDiagonal (1 + rho) (1 - rho) alpha := by
  simp only [seedMatrix, rotatedDiagonal_transpose, rotatedDiagonal_mul]
  rw [Real.mul_self_sqrt (by linarith : 0 ≤ 1 + rho),
    Real.mul_self_sqrt (by linarith : 0 ≤ 1 - rho)]

/-- G01: both Gram traces are exactly two. -/
theorem seed_trace {rho : ℝ} (hrl : -1 < rho) (hru : rho < 1) (alpha : ℝ) :
    ((seedMatrix rho alpha)ᵀ * seedMatrix rho alpha).trace = 2 ∧
    (seedMatrix rho alpha * (seedMatrix rho alpha)ᵀ).trace = 2 := by
  have ht : (seedMatrix rho alpha * (seedMatrix rho alpha)ᵀ).trace = 2 := by
    rw [seed_mul_transpose hrl hru, rotatedDiagonal_trace]
    ring
  exact ⟨by rw [Matrix.trace_mul_comm]; exact ht, ht⟩

/-- G01: the determinant formula and its strict positivity. -/
theorem seed_det {rho : ℝ} (hrl : -1 < rho) (hru : rho < 1) (alpha : ℝ) :
    (seedMatrix rho alpha).det = Real.sqrt (1 - rho ^ 2) ∧
    0 < (seedMatrix rho alpha).det := by
  obtain ⟨hp, hm⟩ := seed_diagonal_positive hrl hru
  rw [seedMatrix, rotatedDiagonal_det]
  constructor
  · rw [← Real.sqrt_mul (by linarith : 0 ≤ 1 + rho)]
    congr 1
    ring
  · exact mul_pos hp hm

/-- G20: multiplying the seed gives precisely the displayed shape entries. -/
theorem angle_shape_entries {rho : ℝ} (hrl : -1 < rho) (hru : rho < 1) (alpha : ℝ) :
    (1 / 2 : ℝ) • (seedMatrix rho alpha * (seedMatrix rho alpha)ᵀ) = angleShape rho alpha := by
  rw [seed_mul_transpose hrl hru, rotatedDiagonal_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [angleShape, Real.sin_two_mul, Real.cos_two_mul] <;>
    nlinarith [Real.sin_sq_add_cos_sq alpha]

/-- G20: equality of the sine/cosine pair at doubled angles is exactly a π congruence. -/
theorem doubled_trig_eq_iff (beta alpha : ℝ) :
    (Real.cos (2 * beta) = Real.cos (2 * alpha) ∧
      Real.sin (2 * beta) = Real.sin (2 * alpha)) ↔ InPiZ (beta - alpha) := by
  constructor
  · rintro ⟨hc, hs⟩
    have hcos : Real.cos (2 * (beta - alpha)) = 1 := by
      rw [mul_sub, Real.cos_sub, hc, hs]
      nlinarith [Real.sin_sq_add_cos_sq (2 * alpha)]
    obtain ⟨k, hk⟩ := (cos_eq_one_iff_two_pi _).mp hcos
    exact ⟨k, by linarith⟩
  · rintro ⟨k, hk⟩
    have he : 2 * beta = 2 * alpha + (k : ℝ) * (2 * Real.pi) := by linarith
    rw [he]
    exact ⟨Real.cos_add_int_mul_two_pi _ k, Real.sin_add_int_mul_two_pi _ k⟩

/-- G20: rho ≠ 0 is necessary; its sign is otherwise unrestricted. -/
theorem angle_shape_eq_iff {rho : ℝ} (hr : rho ≠ 0) (beta alpha : ℝ) :
    angleShape rho beta = angleShape rho alpha ↔ InPiZ (beta - alpha) := by
  rw [← doubled_trig_eq_iff]
  constructor
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
    simp [angleShape, hr] at h00 h01
    exact ⟨h00, h01⟩
  · rintro ⟨hc, hs⟩
    simp [angleShape, hc, hs]

/-- G20: covariance under either allowed normal reflection sign. -/
theorem normal_reflection_shape (rho alpha chi : ℝ) (hx : IsSign chi) :
    normalReflection chi * angleShape rho alpha * (normalReflection chi)ᵀ =
      angleShape rho (chi * alpha) := by
  rcases hx with rfl | rfl <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [normalReflection, angleShape, Matrix.mul_apply, Fin.sum_univ_two,
      show ∀ a : ℝ, 2 * -a = -(2 * a) by intro a; ring, Real.cos_neg, Real.sin_neg] <;> ring

end Grad.GeometryClosure
