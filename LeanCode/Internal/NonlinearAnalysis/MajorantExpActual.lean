import MajorantExpBound
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

/-!
# NG_F06 / N3: the coefficient words as actual bounded multilinear maps

This is the analytic carrier bridge missing from the initial placement-bound
draft.  The ordered `p`-fold coefficient word is bundled as a continuous
`p`-linear map.  Its diagonal is exactly the accepted graded power, hence the
accepted exponential coefficient, and Mathlib's diagonal theorem identifies
its actual top Fréchet derivative with the permutation sum.

The analogous Q8 bridge cannot be stated on `TameCoefficient`: that accepted
all-grade carrier currently has seminorms but no fixed-grade normed-space
instance.  This file deliberately does not choose a replacement Q8 norm.
-/

noncomputable section

open scoped BigOperators ContDiff

namespace Grad.CoefficientMajorants

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000

open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity Grad.GaugeCoefficients.Physical.Frame
open Grad.Constraints.Seed

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
  {grade dimension : ℕ}

abbrev FixedCoefficient :=
  Coefficient L sigma gamma ell grade dimension dimension

local instance coefficientActualComplexSpace : NormedSpace ℂ
    (FixedCoefficient (L := L) (sigma := sigma) (gamma := gamma) (ell := ell)
      (grade := grade) (dimension := dimension)) := inferInstance

local instance coefficientActualRealSpace : NormedSpace ℝ
    (FixedCoefficient (L := L) (sigma := sigma) (gamma := gamma) (ell := ell)
      (grade := grade) (dimension := dimension)) := inferInstance

local instance coefficientActualScalarTower : IsScalarTower ℝ ℂ
    (FixedCoefficient (L := L) (sigma := sigma) (gamma := gamma) (ell := ell)
      (grade := grade) (dimension := dimension)) := inferInstance

/-- Generic bounded multilinear words for a bounded bilinear operation. -/
noncomputable def continuousMultilinearWord {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (operation : E →L[ℂ] E →L[ℂ] E) (unit : E) :
    (p : ℕ) → ContinuousMultilinearMap ℂ (fun _ : Fin p => E) E
  | 0 => ContinuousMultilinearMap.constOfIsEmpty ℂ _ unit
  | p + 1 =>
      let previous := continuousMultilinearWord operation unit p
      let evaluate :
          ((ContinuousMultilinearMap ℂ (fun _ : Fin p => E) E) →L[ℂ]
              ContinuousMultilinearMap ℂ (fun _ : Fin p => E) E) →L[ℂ]
            ContinuousMultilinearMap ℂ (fun _ : Fin p => E) E :=
        ContinuousLinearMap.apply ℂ _ previous
      let postcompose : E →L[ℂ] ContinuousMultilinearMap ℂ (fun _ : Fin p => E) E :=
        evaluate.comp
          ((ContinuousLinearMap.compContinuousMultilinearMapL ℂ (fun _ : Fin p => E) E E).comp
            operation)
      postcompose.uncurryLeft

/-- The ordered coefficient word, bundled as an actual bounded `p`-linear map.
The recursive `uncurryLeft` construction keeps the written order used by
`gradedCoefficientPower`. -/
noncomputable def compositionWordMultilinear (p : ℕ) :=
  continuousMultilinearWord (leftCompositionOperator admissible grade dimension)
    (gradedIdentityCoefficient L sigma gamma ell grade dimension) p

@[simp] theorem compositionWordMultilinear_apply (p : ℕ)
    (factors : Fin p → FixedCoefficient (L := L) (sigma := sigma) (gamma := gamma)
      (ell := ell) (grade := grade) (dimension := dimension)) :
    compositionWordMultilinear admissible (grade := grade) (dimension := dimension) p factors =
      compositionWord admissible p factors := by
  induction p with
  | zero =>
      rw [compositionWordMultilinear, continuousMultilinearWord,
        ContinuousMultilinearMap.constOfIsEmpty_apply]
      rfl
  | succ p inductionHypothesis =>
      rw [compositionWordMultilinear, continuousMultilinearWord,
        ContinuousLinearMap.uncurryLeft_apply]
      change coefficientComposition admissible grade (factors 0)
          (compositionWordMultilinear admissible (grade := grade) (dimension := dimension) p
            (Fin.tail factors)) = _
      rw [inductionHypothesis]
      rfl

/-- Operator norm of the bundled coefficient word. -/
theorem compositionWordMultilinear_norm_le (p : ℕ) :
    ‖compositionWordMultilinear admissible (grade := grade) (dimension := dimension) p‖ ≤
      ‖gradedIdentityCoefficient L sigma gamma ell grade dimension‖ *
        gradeProductConstant grade ^ p := by
  apply ContinuousMultilinearMap.opNorm_le_bound
    (mul_nonneg (norm_nonneg _) (pow_nonneg (seedProductConstant_nonnegative grade) _))
  intro factors
  rw [compositionWordMultilinear_apply]
  exact compositionWord_norm_le admissible p factors

/-- The diagonal of the bundled word is the accepted graded power. -/
theorem compositionWordMultilinear_diagonal (p : ℕ)
    (base : FixedCoefficient (L := L) (sigma := sigma) (gamma := gamma) (ell := ell)
      (grade := grade) (dimension := dimension)) :
    compositionWordMultilinear admissible (grade := grade) (dimension := dimension) p
        (fun _ => base) =
      gradedCoefficientPower admissible base p := by
  rw [compositionWordMultilinear_apply, compositionWord_const]

/-- The accepted exponential coefficient is exactly the diagonal homogeneous
polynomial attached to the bounded multilinear word. -/
theorem seedExponentialTerm_eq_multilinear_diagonal (p : ℕ)
    (base : FixedCoefficient (L := L) (sigma := sigma) (gamma := gamma) (ell := ell)
      (grade := grade) (dimension := dimension)) :
    seedExponentialTerm admissible base p =
      ((p.factorial : ℂ)⁻¹) •
        compositionWordMultilinear admissible (grade := grade) (dimension := dimension) p
          (fun _ => base) := by
  unfold seedExponentialTerm
  rw [compositionWordMultilinear_diagonal]

/-- Every accepted exponential coefficient is an actual smooth homogeneous
polynomial on the complete fixed-grade coefficient carrier. -/
theorem seedExponentialTerm_contDiff (p : ℕ) :
    ContDiff ℂ ∞ (fun base : FixedCoefficient (L := L) (sigma := sigma) (gamma := gamma)
      (ell := ell) (grade := grade) (dimension := dimension) =>
        seedExponentialTerm admissible base p) := by
  have diagonalSmooth : ContDiff ℂ ∞
      (fun base : FixedCoefficient (L := L) (sigma := sigma) (gamma := gamma)
          (ell := ell) (grade := grade) (dimension := dimension) =>
        compositionWordMultilinear admissible (grade := grade) (dimension := dimension) p
          (fun _ => base)) :=
    (compositionWordMultilinear admissible (grade := grade) (dimension := dimension) p).contDiff.comp
      ((contDiff_pi).2 fun _ => contDiff_id)
  have scaledSmooth := ContDiff.const_smul ((p.factorial : ℂ)⁻¹) diagonalSmooth
  simpa only [seedExponentialTerm_eq_multilinear_diagonal admissible p] using scaledSmooth

/-- The same coefficient maps are smooth for the real Banach calculus used by
NG_F04. -/
theorem seedExponentialTerm_contDiff_real (p : ℕ) :
    ContDiff ℝ ∞ (fun base : FixedCoefficient (L := L) (sigma := sigma) (gamma := gamma)
      (ell := ell) (grade := grade) (dimension := dimension) =>
        seedExponentialTerm admissible base p) :=
  (seedExponentialTerm_contDiff admissible p).restrict_scalars ℝ

/-- Actual top Fréchet derivative of the accepted `p`-th exponential
coefficient.  This is the first genuine operator-derivative bridge: the
derivative is the permutation sum of the bounded coefficient word, rather
than merely a formally declared placement expression. -/
theorem iteratedFDeriv_seedExponentialTerm_top_apply (p : ℕ)
    (base : FixedCoefficient (L := L) (sigma := sigma) (gamma := gamma) (ell := ell)
      (grade := grade) (dimension := dimension))
    (directions : Fin p → FixedCoefficient (L := L) (sigma := sigma) (gamma := gamma)
      (ell := ell) (grade := grade) (dimension := dimension)) :
    (iteratedFDeriv ℂ p (fun x => seedExponentialTerm admissible x p) base) directions =
      ((p.factorial : ℂ)⁻¹) •
        ∑ permutation : Equiv.Perm (Fin p),
          compositionWord admissible p (fun index => directions (permutation index)) := by
  simp_rw [seedExponentialTerm_eq_multilinear_diagonal admissible p]
  have diagonalSmooth : ContDiffAt ℂ p
      (fun x : FixedCoefficient (L := L) (sigma := sigma) (gamma := gamma) (ell := ell)
          (grade := grade) (dimension := dimension) =>
        compositionWordMultilinear admissible (grade := grade) (dimension := dimension) p
          (fun _ => x)) base :=
    ((compositionWordMultilinear admissible (grade := grade) (dimension := dimension) p).contDiff.comp
      ((contDiff_pi).2 fun _ => contDiff_id)).contDiffAt
  rw [iteratedFDeriv_const_smul_apply' diagonalSmooth]
  rw [smul_apply]
  rw [ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal]
  congr 1
  apply Finset.sum_congr rfl
  intro permutation _
  rw [compositionWordMultilinear_apply]

/-- The real Fréchet derivative required by NG_F04 is scalar restriction of
the complex derivative above.  In particular the bridge is on the literal
real-calculus carrier used by `HasLocalOperatorMajorants`. -/
theorem iteratedFDeriv_seedExponentialTerm_real_top (p : ℕ)
    (base : FixedCoefficient (L := L) (sigma := sigma) (gamma := gamma) (ell := ell)
      (grade := grade) (dimension := dimension)) :
    iteratedFDeriv ℝ p (fun x => seedExponentialTerm admissible x p) base =
      (iteratedFDeriv ℂ p (fun x => seedExponentialTerm admissible x p) base).restrictScalars ℝ := by
  symm
  simpa only [Function.comp_apply] using
    ((seedExponentialTerm_contDiff admissible p).contDiffAt.of_le
      (show (p : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).restrictScalars_iteratedFDeriv
      (𝕜 := ℝ)

/-- The actual top-order operator derivative has the sharp factorial-cancelled
bound furnished by the bounded multilinear word. -/
theorem iteratedFDeriv_seedExponentialTerm_top_norm_le (p : ℕ)
    (base : FixedCoefficient (L := L) (sigma := sigma) (gamma := gamma) (ell := ell)
      (grade := grade) (dimension := dimension)) :
    ‖iteratedFDeriv ℝ p (fun x => seedExponentialTerm admissible x p) base‖ ≤
      ‖gradedIdentityCoefficient L sigma gamma ell grade dimension‖ *
        gradeProductConstant grade ^ p := by
  rw [iteratedFDeriv_seedExponentialTerm_real_top admissible p base]
  have restrictNorm :
      ‖(iteratedFDeriv ℂ p (fun x => seedExponentialTerm admissible x p) base).restrictScalars ℝ‖ =
        ‖iteratedFDeriv ℂ p (fun x => seedExponentialTerm admissible x p) base‖ :=
    ContinuousMultilinearMap.norm_restrictScalars _
  rw [restrictNorm]
  apply ContinuousMultilinearMap.opNorm_le_bound
    (mul_nonneg (norm_nonneg _) (pow_nonneg (seedProductConstant_nonnegative grade) _))
  intro directions
  rw [iteratedFDeriv_seedExponentialTerm_top_apply admissible p base directions,
    norm_smul, norm_inv, Complex.norm_natCast]
  have factorialNonneg : 0 ≤ ((p.factorial : ℕ) : ℝ)⁻¹ := by positivity
  calc
    ((p.factorial : ℕ) : ℝ)⁻¹ *
        ‖∑ permutation : Equiv.Perm (Fin p),
          compositionWord admissible p (fun index => directions (permutation index))‖
      ≤ ((p.factorial : ℕ) : ℝ)⁻¹ *
          ∑ permutation : Equiv.Perm (Fin p),
            ‖compositionWord admissible p (fun index => directions (permutation index))‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) factorialNonneg
    _ ≤ ((p.factorial : ℕ) : ℝ)⁻¹ *
          ∑ _permutation : Equiv.Perm (Fin p),
            (‖gradedIdentityCoefficient L sigma gamma ell grade dimension‖ *
              gradeProductConstant grade ^ p) * ∏ index, ‖directions index‖ := by
        apply mul_le_mul_of_nonneg_left _ factorialNonneg
        apply Finset.sum_le_sum
        intro permutation _
        have wordBound := compositionWord_norm_le admissible p
          (fun index => directions (permutation index))
        have productEq : ∏ index, ‖directions (permutation index)‖ =
            ∏ index, ‖directions index‖ :=
          Equiv.prod_comp permutation (fun index => ‖directions index‖)
        rwa [productEq] at wordBound
    _ = (‖gradedIdentityCoefficient L sigma gamma ell grade dimension‖ *
          gradeProductConstant grade ^ p) * ∏ index, ‖directions index‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          nsmul_eq_mul]
        have factorialNe : (((p.factorial : ℕ) : ℝ)) ≠ 0 := by positivity
        rw [← mul_assoc, inv_mul_cancel₀ factorialNe, one_mul]

end Grad.CoefficientMajorants
