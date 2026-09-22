import WTCWords

noncomputable section

open Grad.PDEBootstrap
open scoped ContDiff

namespace Grad.WeakTesting.Commutation

def differentiate (direction : Fin 2) (test : Spatial → ℝ) : Spatial → ℝ :=
  fun point => fderiv ℝ test point (spatialDirection direction)

def listDerivative (word : List (Fin 2)) (test : Spatial → ℝ) : Spatial → ℝ :=
  word.foldr differentiate test

theorem differentiate_contDiff (direction : Fin 2) (test : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ test) : ContDiff ℝ ∞ (differentiate direction test) :=
  (contDiff_infty_iff_fderiv.mp smoothness).2.clm_apply contDiff_const

theorem listDerivative_contDiff (word : List (Fin 2)) (test : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ test) : ContDiff ℝ ∞ (listDerivative word test) := by
  induction word with
  | nil => exact smoothness
  | cons direction rest induction => exact differentiate_contDiff direction _ induction

theorem differentiate_commute (first second : Fin 2) (test : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ test) :
    differentiate first (differentiate second test) =
      differentiate second (differentiate first test) := by
  funext point
  have derivativeSmooth : ContDiff ℝ ∞ (fderiv ℝ test) :=
    (contDiff_infty_iff_fderiv.mp smoothness).2
  have derivativeDifferentiable := (contDiff_infty_iff_fderiv.mp derivativeSmooth).1
  change fderiv ℝ (fun point => fderiv ℝ test point (spatialDirection second)) point
      (spatialDirection first) =
    fderiv ℝ (fun point => fderiv ℝ test point (spatialDirection first)) point
      (spatialDirection second)
  rw [fderiv_clm_apply (derivativeDifferentiable point)
      (differentiableAt_const (spatialDirection second)),
    fderiv_clm_apply (derivativeDifferentiable point)
      (differentiableAt_const (spatialDirection first))]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact (smoothness.contDiffAt.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eq _ _

theorem listDerivative_perm {first second : List (Fin 2)} (permuted : first.Perm second)
    (test : Spatial → ℝ) (smoothness : ContDiff ℝ ∞ test) :
    listDerivative first test = listDerivative second test := by
  induction permuted with
  | nil => rfl
  | cons direction permuted induction => exact congrArg (differentiate direction) induction
  | swap first second rest =>
    exact differentiate_commute second first _ (listDerivative_contDiff rest test smoothness)
  | trans first second inductionFirst inductionSecond => exact inductionFirst.trans inductionSecond

theorem listDerivative_ofFn (rank : ℕ) (word : Fin rank → Fin 2) (test : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ test) :
    listDerivative (List.ofFn word) test = orderedTestDerivative rank word test := by
  induction rank with
  | zero => rfl
  | succ rank induction =>
    rw [List.ofFn_succ]
    change differentiate (word 0) (listDerivative (List.ofFn (Fin.tail word)) test) = _
    rw [induction]
    funext point
    have derivativeDifferentiable := smoothness.differentiable_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl rank)
    exact ((derivativeDifferentiable point).iteratedFDeriv_succ_apply_left'
      (m := fun position => spatialDirection (word position))).symm

theorem orderedTestDerivative_permutation (rank : ℕ) (word : Fin rank → Fin 2)
    (permutation : Equiv.Perm (Fin rank)) (test : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ test) :
    orderedTestDerivative rank (word ∘ permutation) test = orderedTestDerivative rank word test := by
  rw [← listDerivative_ofFn rank (word ∘ permutation) test smoothness,
    ← listDerivative_ofFn rank word test smoothness]
  exact listDerivative_perm (permutation.ofFn_comp_perm word) test smoothness

theorem orderedTestDerivative_sameCounts (rank : ℕ) (first second : Fin rank → Fin 2)
    (same : SameCounts first second) (test : Spatial → ℝ) (smoothness : ContDiff ℝ ∞ test) :
    orderedTestDerivative rank first test = orderedTestDerivative rank second test := by
  obtain ⟨permutation, rfl⟩ := wordPermutation rank first second same
  exact (orderedTestDerivative_permutation rank first permutation test smoothness).symm

theorem smooth : SmoothGoal :=
  ⟨orderedTestDerivative_permutation, orderedTestDerivative_sameCounts⟩

theorem orderedTestDerivative_canonical (zeros ones : ℕ) (word : Fin (zeros + ones) → Fin 2)
    (zeroCount : directionCount word 0 = zeros) (oneCount : directionCount word 1 = ones)
    (test : Spatial → ℝ) (smoothness : ContDiff ℝ ∞ test) :
    orderedTestDerivative (zeros + ones) word test =
      orderedTestDerivative (zeros + ones) (canonicalWord zeros ones) test :=
  orderedTestDerivative_sameCounts _ _ _ (sameCounts_canonical zeros ones word zeroCount oneCount)
    test smoothness

theorem canonical : CanonicalGoal :=
  fun zeros ones => ⟨canonicalWord_count_zero zeros ones, canonicalWord_count_one zeros ones,
    orderedTestDerivative_canonical zeros ones⟩

end Grad.WeakTesting.Commutation
