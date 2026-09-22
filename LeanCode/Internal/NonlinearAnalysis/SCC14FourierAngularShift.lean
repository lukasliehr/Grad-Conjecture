import SCC13MappedCofactor
import TRM9LiteralFourierShift

noncomputable section
open scoped BigOperators

namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarAngular

def polarFourierMass {dimension : ℕ} (parameters : PhaseParameters) (tangential : ℕ) (radius : ℝ)
    (sequence : ℤ × ℤ → ComplexEuclidean dimension) (mode : ℤ × ℤ) : ℝ :=
  coefficientRadialEnvelope parameters mode.2 radius * annularFrequency mode.1 mode.2 ^ tangential *
    ‖sequence mode‖

theorem polarFourierMass_nonnegative {dimension : ℕ} (parameters : PhaseParameters)
    (tangential : ℕ) (radius : ℝ) (sequence : ℤ × ℤ → ComplexEuclidean dimension) (mode : ℤ × ℤ) :
    0 ≤ polarFourierMass parameters tangential radius sequence mode :=
  mul_nonneg (mul_nonneg (coefficientRadialEnvelope_pos _ _ _).le
    (pow_nonneg (annularFrequency_nonnegative _ _) _)) (norm_nonneg _)

theorem polarFourierMass_shift_le {dimension : ℕ} (parameters : PhaseParameters)
    (tangential : ℕ) (radius : ℝ) (sequence : ℤ × ℤ → ComplexEuclidean dimension)
    (shift : ℤ) (mode : ℤ × ℤ) :
    polarFourierMass parameters tangential radius (sequence ∘ angularModeTranslation shift) mode ≤
      (1 + |(shift : ℝ)|) ^ tangential *
        polarFourierMass parameters tangential radius sequence (angularModeTranslation shift mode) := by
  have bound := pow_le_pow_left₀ (annularFrequency_nonnegative mode.1 mode.2)
    (annularFrequency_shift_le mode.1 mode.2 shift) tangential
  have weighted := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left bound (coefficientRadialEnvelope_pos parameters mode.2 radius).le)
    (norm_nonneg (sequence (angularModeTranslation shift mode)))
  exact weighted.trans_eq (by simp only [polarFourierMass, angularModeTranslation_apply, mul_pow]; ring)

theorem polarFourierMass_shift_summable {dimension : ℕ} (parameters : PhaseParameters)
    (tangential : ℕ) (radius : ℝ) (sequence : ℤ × ℤ → ComplexEuclidean dimension)
    (summable : Summable (polarFourierMass parameters tangential radius sequence)) (shift : ℤ) :
    Summable (polarFourierMass parameters tangential radius (sequence ∘ angularModeTranslation shift)) :=
  Summable.of_nonneg_of_le (polarFourierMass_nonnegative _ _ _ _)
    (polarFourierMass_shift_le parameters tangential radius sequence shift)
    (((angularModeTranslation shift).summable_iff.mpr summable).mul_left _)

theorem polarFourierMass_shift_bound {dimension : ℕ} (parameters : PhaseParameters)
    (tangential : ℕ) (radius : ℝ) (sequence : ℤ × ℤ → ComplexEuclidean dimension)
    (summable : Summable (polarFourierMass parameters tangential radius sequence)) (shift : ℤ) :
    ∑' mode, polarFourierMass parameters tangential radius (sequence ∘ angularModeTranslation shift) mode ≤
      (1 + |(shift : ℝ)|) ^ tangential * ∑' mode, polarFourierMass parameters tangential radius sequence mode := by
  have shifted := (angularModeTranslation shift).summable_iff.mpr summable
  have bound := (polarFourierMass_shift_summable parameters tangential radius sequence summable shift).tsum_le_tsum
    (polarFourierMass_shift_le parameters tangential radius sequence shift) (shifted.mul_left _)
  simpa only [tsum_mul_left, (angularModeTranslation shift).tsum_eq] using bound

theorem polarFourierMass_sum_le {Index : Type*} [Fintype Index] {dimension : ℕ}
    (parameters : PhaseParameters) (tangential : ℕ) (radius : ℝ)
    (sequences : Index → ℤ × ℤ → ComplexEuclidean dimension) (mode : ℤ × ℤ) :
    polarFourierMass parameters tangential radius (fun mode => ∑ index, sequences index mode) mode ≤
      ∑ index, polarFourierMass parameters tangential radius (sequences index) mode := by
  have weighted := mul_le_mul_of_nonneg_left (norm_sum_le (Finset.univ) (fun index => sequences index mode))
    (mul_nonneg (coefficientRadialEnvelope_pos parameters mode.2 radius).le
      (pow_nonneg (annularFrequency_nonnegative mode.1 mode.2) tangential))
  simpa only [polarFourierMass, Finset.mul_sum] using weighted

theorem polarFourierMass_sum_summable {Index : Type*} [Fintype Index] {dimension : ℕ}
    (parameters : PhaseParameters) (tangential : ℕ) (radius : ℝ)
    (sequences : Index → ℤ × ℤ → ComplexEuclidean dimension)
    (summable : ∀ index, Summable (polarFourierMass parameters tangential radius (sequences index))) :
    Summable (polarFourierMass parameters tangential radius (fun mode => ∑ index, sequences index mode)) :=
  Summable.of_nonneg_of_le (polarFourierMass_nonnegative _ _ _ _)
    (polarFourierMass_sum_le parameters tangential radius sequences)
    (summable_sum (fun index _ => summable index))

theorem polarFourierMass_sum_bound {Index : Type*} [Fintype Index] {dimension : ℕ}
    (parameters : PhaseParameters) (tangential : ℕ) (radius : ℝ)
    (sequences : Index → ℤ × ℤ → ComplexEuclidean dimension)
    (summable : ∀ index, Summable (polarFourierMass parameters tangential radius (sequences index))) :
    ∑' mode, polarFourierMass parameters tangential radius (fun mode => ∑ index, sequences index mode) mode ≤
      ∑ index, ∑' mode, polarFourierMass parameters tangential radius (sequences index) mode := by
  have bound := (polarFourierMass_sum_summable parameters tangential radius sequences summable).tsum_le_tsum
    (polarFourierMass_sum_le parameters tangential radius sequences) (summable_sum (fun index _ => summable index))
  simpa only [Summable.tsum_finsetSum (fun index _ => summable index)] using bound

end Grad.SourceCollarCoefficients
