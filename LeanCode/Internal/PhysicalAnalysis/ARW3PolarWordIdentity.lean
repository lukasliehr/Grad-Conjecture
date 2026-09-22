import ARW2LocalRadialCalculus

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators
namespace Grad.ActualRadialWords
open Grad.ClosedJets Grad.CartesianState Grad.CollarCartesian Grad.BoundaryLift

/-- Literal number of radial or angular directions in an ordered product-basis word. -/
def wordCount {order : ℕ} (word : CartesianWord order) (coordinate : Fin 2) : ℕ :=
  ∑ position : Fin order, if word position = coordinate then 1 else 0

theorem wordCount_succ {order : ℕ} (word : CartesianWord (order + 1)) (coordinate : Fin 2) :
    wordCount word coordinate = (if word 0 = coordinate then 1 else 0) + wordCount (Fin.tail word) coordinate := by
  exact Fin.sum_univ_succ _

theorem wordCount_total {order : ℕ} (word : CartesianWord order) :
    wordCount word 0 + wordCount word 1 = order := by
  rw [wordCount, wordCount, ← Finset.sum_add_distrib]
  calc
    _ = ∑ _position : Fin order, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro position _
      generalize value : word position = coordinate
      fin_cases coordinate <;> simp
    _ = _ := by simp

def wordFactor {order : ℕ} (mode : ℤ) (word : CartesianWord order) : ℂ :=
  (Complex.I * (mode : ℂ)) ^ wordCount word 1 * (-1 : ℂ) ^ wordCount word 0

theorem polarMode_word_derivative (mode : ℤ) (profile : ℝ → ComplexEuclidean 1)
    (smooth : ContDiffOn ℝ ∞ profile (Icc (1 / 2 : ℝ) 1))
    (order : ℕ) (word : CartesianWord order) (point : ℝ × ℝ) (inside : point ∈ openHalfCollar) :
    iteratedFDeriv ℝ order (polarMode mode profile) point
      (fun position => productBasis (word position)) =
        wordFactor mode word • polarRadialDerivative mode profile (wordCount word 0) point := by
  induction order generalizing point with
  | zero => simp [wordFactor, wordCount, polarRadialDerivative, polarMode, iteratedDerivWithin_zero]
  | succ order induction =>
    have smoothAt := (polarMode_smoothOn mode profile smooth).contDiffAt
      (openHalfCollar_open.mem_nhds inside)
    have tensorDiff := smoothAt.differentiableAt_iteratedFDeriv
      (m := order) (by exact_mod_cast (WithTop.coe_lt_top order : (order : ℕ∞) < ⊤))
    rw [tensorDiff.iteratedFDeriv_succ_apply_left']
    have agreement :
        (fun next => iteratedFDeriv ℝ order (polarMode mode profile) next
          (Fin.tail (fun position => productBasis (word position)))) =ᶠ[𝓝 point]
        (fun next => wordFactor mode (Fin.tail word) •
          polarRadialDerivative mode profile (wordCount (Fin.tail word) 0) next) := by
      filter_upwards [openHalfCollar_open.mem_nhds inside] with next nextIn
      exact induction (Fin.tail word) next nextIn
    rw [agreement.fderiv_eq]
    have base := polarRadialDerivative_hasFDerivAt mode profile smooth
      (wordCount (Fin.tail word) 0) point inside
    have scaled := (base.const_smul (wordFactor mode (Fin.tail word))).fderiv
    rw [← base.fderiv] at scaled
    change fderiv ℝ (fun next => wordFactor mode (Fin.tail word) •
      polarRadialDerivative mode profile (wordCount (Fin.tail word) 0) next) point = _ at scaled
    rw [scaled, smul_apply,
      polarRadialDerivative_coordinate mode profile smooth _ point inside]
    simp only [wordFactor]
    rw [wordCount_succ word 1, wordCount_succ word 0]
    by_cases first : word 0 = 0
    · simp [first, pow_add, mul_smul, Nat.add_comm]
    · have firstOne : word 0 = 1 := by omega
      simp only [firstOne, one_ne_zero, if_false, if_true, zero_add, pow_add, pow_one]
      simp only [← mul_smul]
      congr 1
      ring

end Grad.ActualRadialWords
