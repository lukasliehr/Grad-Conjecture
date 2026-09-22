import AKDN8GenuineBalancedPhaseAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
namespace Grad.OriginalCartesianTameEstimate

section FiniteBilinear
variable {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem vectorEulerWithin_jetDerivative (domain : Set ℝ) (unique : UniqueDiffOn ℝ domain)
    (field : ℝ → E) (rank : ℕ) (smooth : ContDiffOn ℝ (rank+1 : ℕ) field domain)
    (radius : ℝ) (inside : radius ∈ domain) (nonzero : radius ≠ 0) :
    HasDerivWithinAt (vectorEulerWithinIteratedDerivative domain rank field)
      (radius⁻¹ • vectorEulerWithinIteratedDerivative domain (rank+1) field radius) domain radius := by
  have regular := vectorEulerWithin_smooth domain unique field rank 1
    (by simpa only [Nat.add_comm 1 rank] using smooth)
  have derivative := (regular.differentiableOn (by norm_num) radius inside).hasDerivWithinAt
  change HasDerivWithinAt _ (radius⁻¹ • (radius • derivWithin
    (vectorEulerWithinIteratedDerivative domain rank field) domain radius)) domain radius
  simpa only [inv_smul_smul₀ nonzero] using derivative

/-- The finite polynomial needs derivatives only at the ranks actually
present. A qualitative reserve beyond the requested order is sufficient. -/
theorem bilinearEulerPolynomial_hasDerivWithinAt_of_mem (bilinear : E →L[ℝ] F →L[ℝ] G)
    (domain : Set ℝ) (first : ℕ → ℝ → E) (second : ℕ → ℝ → F) (radius : ℝ)
    (terms : List (ℕ × ℕ))
    (firstDerivative : ∀ term ∈ terms, HasDerivWithinAt (first term.1)
      (radius⁻¹ • first (term.1+1) radius) domain radius)
    (secondDerivative : ∀ term ∈ terms, HasDerivWithinAt (second term.2)
      (radius⁻¹ • second (term.2+1) radius) domain radius) :
    HasDerivWithinAt (bilinearEulerPolynomial bilinear first second terms)
      (radius⁻¹ • bilinearEulerPolynomial bilinear first second (eulerLeibnizStep terms) radius) domain radius := by
  induction terms with
  | nil =>
      change HasDerivWithinAt (fun _ => (0 : G)) (radius⁻¹ • 0) domain radius
      rw [smul_zero]
      exact hasDerivWithinAt_const radius domain 0
  | cons term terms previous =>
      have tail := previous (fun query member => firstDerivative query (List.mem_cons_of_mem term member))
        (fun query member => secondDerivative query (List.mem_cons_of_mem term member))
      change HasDerivWithinAt (fun point => bilinear (first term.1 point) (second term.2 point)+
        bilinearEulerPolynomial bilinear first second terms point)
        (radius⁻¹ • (bilinear (first (term.1+1) radius) (second term.2 radius)+
          (bilinear (first term.1 radius) (second (term.2+1) radius)+
            bilinearEulerPolynomial bilinear first second (eulerLeibnizStep terms) radius))) domain radius
      apply ((actualBilinear_hasDerivWithinAt bilinear domain _ _ radius _ _
        (firstDerivative term List.mem_cons_self) (secondDerivative term List.mem_cons_self)).add tail).congr_deriv
      simp only [map_smul,smul_apply,smul_add]
      abel

/-- Genuine finite-order closed-collar Leibniz formula. Every ordered
allocation has total rank exactly the requested derivative order. -/
theorem vectorEulerWithin_bilinear (bilinear : E →L[ℝ] F →L[ℝ] G)
    (domain : Set ℝ) (unique : UniqueDiffOn ℝ domain) (nonzero : ∀ radius ∈ domain, radius ≠ 0)
    (first : ℝ → E) (second : ℝ → F) (rank : ℕ)
    (firstSmooth : ContDiffOn ℝ rank first domain) (secondSmooth : ContDiffOn ℝ rank second domain) :
    EqOn (vectorEulerWithinIteratedDerivative domain rank (fun point => bilinear (first point) (second point)))
      (bilinearEulerPolynomial bilinear
        (fun order => vectorEulerWithinIteratedDerivative domain order first)
        (fun order => vectorEulerWithinIteratedDerivative domain order second) (eulerLeibnizTerms rank)) domain := by
  induction rank with
  | zero =>
      intro radius _
      change _ = _+0
      exact (add_zero _).symm
  | succ rank previous =>
      have lower := previous (firstSmooth.of_le (by simp)) (secondSmooth.of_le (by simp))
      intro radius inside
      change radius • derivWithin (vectorEulerWithinIteratedDerivative domain rank
        (fun point => bilinear (first point) (second point))) domain radius = _
      rw [derivWithin_congr lower (lower inside)]
      have derivative := bilinearEulerPolynomial_hasDerivWithinAt_of_mem bilinear domain
        (fun order => vectorEulerWithinIteratedDerivative domain order first)
        (fun order => vectorEulerWithinIteratedDerivative domain order second) radius (eulerLeibnizTerms rank) ?_ ?_
      · rw [derivative.derivWithin (unique radius inside)]
        exact smul_inv_smul₀ (nonzero radius inside) _
      · intro term member
        have allocated := eulerLeibnizTerms_rank rank term member
        exact vectorEulerWithin_jetDerivative domain unique first term.1
          (firstSmooth.of_le (by exact_mod_cast (show term.1+1 ≤ rank+1 by omega))) radius inside (nonzero radius inside)
      · intro term member
        have allocated := eulerLeibnizTerms_rank rank term member
        exact vectorEulerWithin_jetDerivative domain unique second term.2
          (secondSmooth.of_le (by exact_mod_cast (show term.2+1 ≤ rank+1 by omega))) radius inside (nonzero radius inside)

/-- Estimate the already differentiated polynomial term by term. The
consumer can retain each complementary coefficient/input allocation. -/
theorem bilinearEulerPolynomial_norm (bilinear : E →L[ℝ] F →L[ℝ] G)
    (first : ℕ → ℝ → E) (second : ℕ → ℝ → F) (terms : List (ℕ × ℕ)) (radius : ℝ) :
    ‖bilinearEulerPolynomial bilinear first second terms radius‖ ≤
      eulerAllocationSum (fun left right => ‖bilinear (first left radius) (second right radius)‖) terms := by
  induction terms with
  | nil => exact (norm_zero).le
  | cons term terms previous => exact (norm_add_le _ _).trans (add_le_add (le_refl _) previous)

end FiniteBilinear
end Grad.OriginalCartesianTameEstimate
