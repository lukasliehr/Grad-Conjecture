import SP1Bilinear
import WTCWords
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section

open Grad.PDEBootstrap Grad.GenericCarriers
open scoped ContDiff Topology

namespace Grad.RepresentedKernel.SpatialProduct

def directionDerivative {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (direction : Fin 2) (function : Spatial → Value) : Spatial → Value :=
  fun point => fderiv ℝ function point (spatialDirection direction)

def listDerivative {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (word : List (Fin 2)) (function : Spatial → Value) : Spatial → Value :=
  word.foldr directionDerivative function

theorem directionDerivative_smooth {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {domain : Set Spatial} (openDomain : IsOpen domain) (direction : Fin 2)
    {function : Spatial → Value} (smooth : ContDiffOn ℝ ∞ function domain) :
    ContDiffOn ℝ ∞ (directionDerivative direction function) domain :=
  ((contDiffOn_infty_iff_fderiv_of_isOpen openDomain).mp smooth).2.clm_apply contDiffOn_const

theorem listDerivative_smooth {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {domain : Set Spatial} (openDomain : IsOpen domain) (word : List (Fin 2))
    {function : Spatial → Value} (smooth : ContDiffOn ℝ ∞ function domain) :
    ContDiffOn ℝ ∞ (listDerivative word function) domain := by
  induction word with
  | nil => exact smooth
  | cons direction rest inductionHypothesis =>
    exact directionDerivative_smooth openDomain direction inductionHypothesis

theorem directionDerivative_congr {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {domain : Set Spatial} (openDomain : IsOpen domain) (direction : Fin 2)
    {first second : Spatial → Value} (agree : Set.EqOn first second domain) :
    Set.EqOn (directionDerivative direction first) (directionDerivative direction second) domain := by
  intro point inside
  have localEquality : first =ᶠ[𝓝 point] second :=
    Filter.eventually_of_mem (openDomain.mem_nhds inside) agree
  exact congrArg (fun derivative : Spatial →L[ℝ] Value => derivative (spatialDirection direction))
    localEquality.fderiv_eq

theorem directionDerivative_commute {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {domain : Set Spatial} (openDomain : IsOpen domain) (first second : Fin 2)
    {function : Spatial → Value} (smooth : ContDiffOn ℝ ∞ function domain) :
    Set.EqOn (directionDerivative first (directionDerivative second function))
      (directionDerivative second (directionDerivative first function)) domain := by
  intro point inside
  have localSmooth := smooth.contDiffAt (openDomain.mem_nhds inside)
  have derivativeSmooth := ((contDiffOn_infty_iff_fderiv_of_isOpen openDomain).mp smooth).2
  have derivativeDifferentiable :=
    (derivativeSmooth.contDiffAt (openDomain.mem_nhds inside)).differentiableAt (by simp)
  change fderiv ℝ (fun source => fderiv ℝ function source (spatialDirection second)) point
      (spatialDirection first) =
    fderiv ℝ (fun source => fderiv ℝ function source (spatialDirection first)) point
      (spatialDirection second)
  rw [fderiv_clm_apply derivativeDifferentiable (differentiableAt_const (spatialDirection second)),
    fderiv_clm_apply derivativeDifferentiable (differentiableAt_const (spatialDirection first))]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
  exact (localSmooth.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eq _ _

theorem listDerivative_perm {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {domain : Set Spatial} (openDomain : IsOpen domain) {first second : List (Fin 2)}
    (permuted : first.Perm second) {function : Spatial → Value}
    (smooth : ContDiffOn ℝ ∞ function domain) :
    Set.EqOn (listDerivative first function) (listDerivative second function) domain := by
  induction permuted with
  | nil => exact fun _ _ => rfl
  | cons direction permuted inductionHypothesis =>
    exact directionDerivative_congr openDomain direction inductionHypothesis
  | swap first second rest =>
    exact directionDerivative_commute openDomain second first (listDerivative_smooth openDomain rest smooth)
  | trans first second inductionFirst inductionSecond => exact inductionFirst.trans inductionSecond

theorem listDerivative_ofFn {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {domain : Set Spatial} (openDomain : IsOpen domain) (rank : ℕ) (word : Word rank)
    {function : Spatial → Value} (smooth : ContDiffOn ℝ ∞ function domain) :
    Set.EqOn (listDerivative (List.ofFn word) function) (wordDerivative rank word function) domain := by
  induction rank with
  | zero => exact fun _ _ => rfl
  | succ rank inductionHypothesis =>
    intro point inside
    rw [List.ofFn_succ]
    have congruence := directionDerivative_congr openDomain (word 0)
      (inductionHypothesis (Fin.tail word)) inside
    refine congruence.trans ?_
    exact ((differentiable_iterated (smooth.contDiffAt (openDomain.mem_nhds inside)) rank).iteratedFDeriv_succ_apply_left'
      (m := fun position => spatialDirection (word position))).symm

theorem wordDerivative_permutation {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {domain : Set Spatial} (openDomain : IsOpen domain) (rank : ℕ) (word : Word rank)
    (permutation : Equiv.Perm (Fin rank)) {function : Spatial → Value}
    (smooth : ContDiffOn ℝ ∞ function domain) :
    Set.EqOn (wordDerivative rank (word ∘ permutation) function) (wordDerivative rank word function) domain :=
  (listDerivative_ofFn openDomain rank (word ∘ permutation) smooth).symm.trans
    ((listDerivative_perm openDomain (permutation.ofFn_comp_perm word) smooth).trans
      (listDerivative_ofFn openDomain rank word smooth))

theorem wordDerivative_sameCounts {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {domain : Set Spatial} (openDomain : IsOpen domain) (rank : ℕ) (first second : Word rank)
    (same : Grad.WeakTesting.Commutation.SameCounts first second) {function : Spatial → Value}
    (smooth : ContDiffOn ℝ ∞ function domain) :
    Set.EqOn (wordDerivative rank first function) (wordDerivative rank second function) domain := by
  obtain ⟨permutation, rfl⟩ := Grad.WeakTesting.Commutation.wordPermutation rank first second same
  exact (wordDerivative_permutation openDomain rank first permutation smooth).symm

theorem wordDerivative_canonical {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {domain : Set Spatial} (openDomain : IsOpen domain) (zeros ones : ℕ) (word : Word (zeros + ones))
    (zeroCount : Grad.WeakTesting.Commutation.directionCount word 0 = zeros)
    (oneCount : Grad.WeakTesting.Commutation.directionCount word 1 = ones)
    {function : Spatial → Value} (smooth : ContDiffOn ℝ ∞ function domain) :
    Set.EqOn (wordDerivative (zeros + ones) word function)
      (wordDerivative (zeros + ones) (Grad.WeakTesting.Commutation.canonicalWord zeros ones) function) domain :=
  wordDerivative_sameCounts openDomain _ _ _
    (Grad.WeakTesting.Commutation.sameCounts_canonical zeros ones word zeroCount oneCount) smooth

end Grad.RepresentedKernel.SpatialProduct
