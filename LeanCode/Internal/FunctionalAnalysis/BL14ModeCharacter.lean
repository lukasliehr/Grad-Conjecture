import BL13PolarMode

noncomputable section

open Set
open scoped BigOperators ContDiff

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

theorem cellExponential_add (mode : ℤ) (first second : ℝ) :
    cellExponential mode (first + second) = cellExponential mode first * cellExponential mode second := by
  unfold cellExponential
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem polarModeField_angular_translation {dimension : ℕ} (parameters : PhaseParameters) (mode : ℤ × ℤ)
    (value : ComplexEuclidean dimension) (angle : ℝ) (point : ℝ × ℝ) :
    polarModeField parameters mode value (point + (0, angle)) =
      cellExponential mode.1 angle • polarModeField parameters mode value point := by
  simp only [polarModeField, Prod.fst_add, Prod.snd_add, add_zero, cellExponential_add, mul_smul]
  rw [smul_comm (cellExponential mode.1 point.2), smul_comm (conjugatedProfile parameters mode point.1)]

theorem polarModeField_iterated_character {dimension : ℕ} (parameters : PhaseParameters) (mode : ℤ × ℤ)
    (value : ComplexEuclidean dimension) (order : ℕ) (time angle : ℝ) :
    iteratedFDeriv ℝ order (polarModeField parameters mode value) (time, angle) =
      cellExponential mode.1 angle • iteratedFDeriv ℝ order (polarModeField parameters mode value) (time, 0) := by
  have representation : (fun point : ℝ × ℝ => polarModeField parameters mode value (point + (0, angle))) =
      fun point => cellExponential mode.1 angle • polarModeField parameters mode value point :=
    funext (polarModeField_angular_translation parameters mode value angle)
  have translated := congrArg (fun field => iteratedFDeriv ℝ order field (time, 0)) representation
  rw [iteratedFDeriv_comp_add_right, iteratedFDeriv_const_smul_apply'
    ((polarModeField_smooth parameters mode value).of_le
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).contDiffAt] at translated
  simpa only [Prod.mk_add_mk, add_zero, zero_add] using translated

theorem polarModeField_word_character {dimension order : ℕ} (parameters : PhaseParameters) (mode : ℤ × ℤ)
    (value : ComplexEuclidean dimension) (word : CartesianWord order) (time angle : ℝ) :
    iteratedFDeriv ℝ order (polarModeField parameters mode value) (time, angle)
        (fun position => productBasis (word position)) =
      fourier mode.1 (angle : CellCircle) •
        iteratedFDeriv ℝ order (polarModeField parameters mode value) (time, 0)
          (fun position => productBasis (word position)) := by
  rw [polarModeField_iterated_character]
  change cellExponential mode.1 angle •
    (iteratedFDeriv ℝ order (polarModeField parameters mode value) (time, 0)
      (fun position => productBasis (word position))) = _
  rw [← cellCharacter_coe]
  rfl

def finitePolarField {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (modes : Finset ℤ) (values : ℤ → ComplexEuclidean dimension) : ℝ × ℝ → ComplexEuclidean dimension :=
  ∑ mode ∈ modes, polarModeField parameters (mode, cell) (values mode)

theorem finitePolarField_smooth {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (modes : Finset ℤ) (values : ℤ → ComplexEuclidean dimension) :
    ContDiff ℝ ∞ (finitePolarField parameters cell modes values) := by
  have expression : finitePolarField parameters cell modes values =
      fun point => ∑ mode ∈ modes, polarModeField parameters (mode, cell) (values mode) point := by
    funext point
    simp only [finitePolarField, Finset.sum_apply]
  rw [expression]
  apply ContDiff.sum
  intro mode _
  exact polarModeField_smooth parameters (mode, cell) (values mode)

theorem finitePolarField_word_expansion {dimension order : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (modes : Finset ℤ) (values : ℤ → ComplexEuclidean dimension)
    (word : CartesianWord order) (time angle : ℝ) :
    iteratedFDeriv ℝ order (finitePolarField parameters cell modes values) (time, angle)
        (fun position => productBasis (word position)) =
      ∑ mode ∈ modes, fourier mode (angle : CellCircle) •
        iteratedFDeriv ℝ order (polarModeField parameters (mode, cell) (values mode)) (time, 0)
          (fun position => productBasis (word position)) := by
  rw [finitePolarField, iteratedFDeriv_sum_apply]
  · rw [sum_apply]
    apply Finset.sum_congr rfl
    intro mode _
    exact polarModeField_word_character parameters (mode, cell) (values mode) word time angle
  · intro mode _
    exact ((polarModeField_smooth parameters (mode, cell) (values mode)).of_le
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).contDiffAt

end Grad.BoundaryLift
