import ARC3HalfReverseRotation
import BL15FiniteParseval

noncomputable section
open Set
open scoped BigOperators ContDiff
namespace Grad.CollarCartesian
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints Grad.BoundaryLift

def profileMode {dimension : ℕ} (mode : ℤ) (profile : ℝ → ComplexEuclidean dimension)
    (point : ℝ × ℝ) : ComplexEuclidean dimension :=
  cellExponential mode point.2 • profile point.1

theorem profileMode_smooth {dimension : ℕ} (mode : ℤ)
    (profile : ℝ → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ profile) :
    ContDiff ℝ ∞ (profileMode mode profile) := by
  exact (angularExponential_smooth mode).smul (smooth.comp contDiff_fst)

theorem profileMode_angular_translation {dimension : ℕ} (mode : ℤ) (profile : ℝ → ComplexEuclidean dimension) (angle : ℝ) (point : ℝ × ℝ) :
    profileMode mode profile (point + (0, angle)) =
      cellExponential mode angle • profileMode mode profile point := by
  simp only [profileMode, Prod.fst_add, Prod.snd_add, add_zero, cellExponential_add, mul_smul]
  rw [smul_comm]

theorem profileMode_iterated_character {dimension : ℕ} (mode : ℤ) (profile : ℝ → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ profile) (order : ℕ) (time angle : ℝ) :
    iteratedFDeriv ℝ order (profileMode mode profile) (time, angle) =
      cellExponential mode angle • iteratedFDeriv ℝ order (profileMode mode profile) (time, 0) := by
  have representation : (fun point : ℝ × ℝ => profileMode mode profile (point + (0, angle))) =
      fun point => cellExponential mode angle • profileMode mode profile point :=
    funext (profileMode_angular_translation mode profile angle)
  have translated := congrArg (fun field => iteratedFDeriv ℝ order field (time, 0)) representation
  rw [iteratedFDeriv_comp_add_right, iteratedFDeriv_const_smul_apply'
    ((profileMode_smooth mode profile smooth).of_le
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).contDiffAt] at translated
  simpa only [Prod.mk_add_mk, add_zero, zero_add] using translated

theorem profileMode_word_character {dimension order : ℕ} (mode : ℤ) (profile : ℝ → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ profile) (word : CartesianWord order) (time angle : ℝ) :
    iteratedFDeriv ℝ order (profileMode mode profile) (time, angle)
        (fun position => productBasis (word position)) =
      fourier mode (angle : CellCircle) •
        iteratedFDeriv ℝ order (profileMode mode profile) (time, 0)
          (fun position => productBasis (word position)) := by
  rw [profileMode_iterated_character mode profile smooth]
  change cellExponential mode angle •
    (iteratedFDeriv ℝ order (profileMode mode profile) (time, 0)
      (fun position => productBasis (word position))) = _
  rw [← cellCharacter_coe]
  rfl

def finiteProfileField {dimension : ℕ} (modes : Finset ℤ) (profiles : ℤ → ℝ → ComplexEuclidean dimension) : ℝ × ℝ → ComplexEuclidean dimension :=
  ∑ mode ∈ modes, profileMode mode (profiles mode)

theorem finiteProfileField_smooth {dimension : ℕ} (modes : Finset ℤ) (profiles : ℤ → ℝ → ComplexEuclidean dimension) (smooth : ∀ mode, ContDiff ℝ ∞ (profiles mode)) :
    ContDiff ℝ ∞ (finiteProfileField modes profiles) := by
  have expression : finiteProfileField modes profiles =
      fun point => ∑ mode ∈ modes, profileMode mode (profiles mode) point := by
    funext point
    simp only [finiteProfileField, Finset.sum_apply]
  rw [expression]
  apply ContDiff.sum
  intro mode _
  exact profileMode_smooth mode (profiles mode) (smooth mode)

theorem finiteProfileField_word_expansion {dimension order : ℕ} (modes : Finset ℤ) (profiles : ℤ → ℝ → ComplexEuclidean dimension) (smooth : ∀ mode, ContDiff ℝ ∞ (profiles mode))
    (word : CartesianWord order) (time angle : ℝ) :
    iteratedFDeriv ℝ order (finiteProfileField modes profiles) (time, angle)
        (fun position => productBasis (word position)) =
      ∑ mode ∈ modes, fourier mode (angle : CellCircle) •
        iteratedFDeriv ℝ order (profileMode mode (profiles mode)) (time, 0)
          (fun position => productBasis (word position)) := by
  rw [finiteProfileField, iteratedFDeriv_sum_apply]
  · rw [sum_apply]
    apply Finset.sum_congr rfl
    intro mode _
    exact profileMode_word_character mode (profiles mode) (smooth mode) word time angle
  · intro mode _
    exact ((profileMode_smooth mode (profiles mode) (smooth mode)).of_le
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).contDiffAt

end Grad.CollarCartesian
