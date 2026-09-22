import AKDD2SameEulerInverseClosure

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set
namespace Grad.OriginalCartesianTameEstimate

section Bilinear
variable {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem actualBilinear_hasDerivWithinAt (bilinear : E →L[ℝ] F →L[ℝ] G)
    (domain : Set ℝ) (first : ℝ → E) (second : ℝ → F) (radius : ℝ)
    (firstSlope : E) (secondSlope : F)
    (firstDerivative : HasDerivWithinAt first firstSlope domain radius)
    (secondDerivative : HasDerivWithinAt second secondSlope domain radius) :
    HasDerivWithinAt (fun point => bilinear (first point) (second point))
      (bilinear firstSlope (second radius)+bilinear (first radius) secondSlope) domain radius := by
  have result := (bilinear.hasFDerivWithinAt_of_bilinear firstDerivative.hasFDerivWithinAt
    secondDerivative.hasFDerivWithinAt).hasDerivWithinAt
  apply result.congr_deriv
  change bilinear (first radius) ((1 : ℝ) • secondSlope)+bilinear ((1 : ℝ) • firstSlope) (second radius) = _
  simp only [one_smul]
  exact add_comm _ _

/-- Exact rectangular/bilinear Euler polynomial, retaining every ordered
rank allocation and multiplicity. -/
def bilinearEulerPolynomial (bilinear : E →L[ℝ] F →L[ℝ] G)
    (first : ℕ → ℝ → E) (second : ℕ → ℝ → F) (terms : List (ℕ × ℕ)) (radius : ℝ) : G :=
  List.rec 0 (fun term _ previous => bilinear (first term.1 radius) (second term.2 radius)+previous) terms

theorem bilinearEulerPolynomial_hasDerivWithinAt (bilinear : E →L[ℝ] F →L[ℝ] G)
    (domain : Set ℝ) (first : ℕ → ℝ → E) (second : ℕ → ℝ → F) (radius : ℝ)
    (firstDerivative : ∀ rank, HasDerivWithinAt (first rank) (radius⁻¹ • first (rank+1) radius) domain radius)
    (secondDerivative : ∀ rank, HasDerivWithinAt (second rank) (radius⁻¹ • second (rank+1) radius) domain radius)
    (terms : List (ℕ × ℕ)) :
    HasDerivWithinAt (bilinearEulerPolynomial bilinear first second terms)
      (radius⁻¹ • bilinearEulerPolynomial bilinear first second (eulerLeibnizStep terms) radius) domain radius := by
  induction terms with
  | nil =>
      change HasDerivWithinAt (fun _ => (0 : G)) (radius⁻¹ • 0) domain radius
      rw [smul_zero]
      exact hasDerivWithinAt_const radius domain 0
  | cons term terms previous =>
      change HasDerivWithinAt (fun point => bilinear (first term.1 point) (second term.2 point)+
        bilinearEulerPolynomial bilinear first second terms point)
        (radius⁻¹ • (bilinear (first (term.1+1) radius) (second term.2 radius)+
          (bilinear (first term.1 radius) (second (term.2+1) radius)+
            bilinearEulerPolynomial bilinear first second (eulerLeibnizStep terms) radius))) domain radius
      apply ((actualBilinear_hasDerivWithinAt bilinear domain _ _ radius _ _
        (firstDerivative term.1) (secondDerivative term.2)).add previous).congr_deriv
      simp only [map_smul,smul_apply,smul_add]
      abel

end Bilinear

end Grad.OriginalCartesianTameEstimate
