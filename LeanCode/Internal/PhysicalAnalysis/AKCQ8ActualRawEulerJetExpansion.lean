import AKCQ7ActualEulerKernelLeibniz

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set
open scoped ContDiff BigOperators
namespace Grad.OriginalCartesianTameEstimate

section Jets
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Raw radial jets retain their derivative index before allocation. -/
def rawEulerMonomial (jets : ℕ → ℝ → E) (rank : ℕ) (radius : ℝ) : E :=
  radius^rank • jets rank radius

def rawEulerMonomialDerivative (jets : ℕ → ℝ → E) (rank : ℕ) (radius : ℝ) : E :=
  ((rank : ℝ)*radius^(rank-1)) • jets rank radius + radius^rank • jets (rank+1) radius

theorem rawEulerMonomial_hasDerivAt (jets : ℕ → ℝ → E)
    (derivative : ∀ rank radius, HasDerivAt (jets rank) (jets (rank+1) radius) radius)
    (rank : ℕ) (radius : ℝ) :
    HasDerivAt (rawEulerMonomial jets rank) (rawEulerMonomialDerivative jets rank radius) radius := by
  change HasDerivAt (fun point => point^rank • jets rank point) _ radius
  apply (((hasDerivAt_id radius).pow rank).smul (derivative rank radius)).congr_deriv
  simp only [rawEulerMonomialDerivative,Pi.pow_apply,id_eq,mul_one]
  exact add_comm _ _

def rawEulerPolynomial (jets : ℕ → ℝ → E) (terms : List (ℕ × ℝ)) (radius : ℝ) : E :=
  List.rec 0 (fun term _ previous => term.2 • rawEulerMonomial jets (term.1+1) radius + previous) terms

def rawEulerPolynomialDerivative (jets : ℕ → ℝ → E) (terms : List (ℕ × ℝ)) (radius : ℝ) : E :=
  List.rec 0 (fun term _ previous => term.2 • rawEulerMonomialDerivative jets (term.1+1) radius + previous) terms

theorem rawEulerPolynomial_hasDerivAt (jets : ℕ → ℝ → E)
    (derivative : ∀ rank radius, HasDerivAt (jets rank) (jets (rank+1) radius) radius)
    (terms : List (ℕ × ℝ)) (radius : ℝ) :
    HasDerivAt (rawEulerPolynomial jets terms) (rawEulerPolynomialDerivative jets terms radius) radius := by
  induction terms with
  | nil => exact hasDerivAt_const radius 0
  | cons term terms previous =>
      change HasDerivAt (fun point => term.2 • rawEulerMonomial jets (term.1+1) point + rawEulerPolynomial jets terms point)
        (term.2 • rawEulerMonomialDerivative jets (term.1+1) radius + rawEulerPolynomialDerivative jets terms radius) radius
      simpa only [Pi.add_def,Pi.smul_apply] using
        ((rawEulerMonomial_hasDerivAt jets derivative (term.1+1) radius).const_smul term.2).add previous

theorem rawEulerMonomial_euler (jets : ℕ → ℝ → E) (rank : ℕ) (radius : ℝ) :
    radius • rawEulerMonomialDerivative jets (rank+1) radius =
      ((rank+1 : ℕ) : ℝ) • rawEulerMonomial jets (rank+1) radius + rawEulerMonomial jets (rank+2) radius := by
  simp only [rawEulerMonomialDerivative,rawEulerMonomial,Nat.add_sub_cancel,pow_succ,smul_add,smul_smul]
  module

theorem rawEulerPolynomial_step (jets : ℕ → ℝ → E) (terms : List (ℕ × ℝ)) (radius : ℝ) :
    rawEulerPolynomial jets (eulerProfilePolynomialStep terms) radius =
      radius • rawEulerPolynomialDerivative jets terms radius := by
  induction terms with
  | nil => simp only [eulerProfilePolynomialStep,rawEulerPolynomial,rawEulerPolynomialDerivative,smul_zero]
  | cons term terms previous =>
      change (term.2*((term.1+1 : ℕ) : ℝ)) • rawEulerMonomial jets (term.1+1) radius +
        (term.2 • rawEulerMonomial jets (term.1+2) radius + rawEulerPolynomial jets (eulerProfilePolynomialStep terms) radius) =
        radius • (term.2 • rawEulerMonomialDerivative jets (term.1+1) radius + rawEulerPolynomialDerivative jets terms radius)
      rw [previous]
      calc
        _ = term.2 • (((term.1+1 : ℕ) : ℝ) • rawEulerMonomial jets (term.1+1) radius +
              rawEulerMonomial jets (term.1+2) radius) + radius • rawEulerPolynomialDerivative jets terms radius := by module
        _ = term.2 • (radius • rawEulerMonomialDerivative jets (term.1+1) radius) +
              radius • rawEulerPolynomialDerivative jets terms radius := by rw [rawEulerMonomial_euler]
        _ = _ := by module

/-- The finite positive-rank expansion equals the genuine iterated Euler
operator on the original raw coefficient, at every radius including zero. -/
theorem vectorEulerIteratedDerivative_rawExpansion (jets : ℕ → ℝ → E)
    (derivative : ∀ rank radius, HasDerivAt (jets rank) (jets (rank+1) radius) radius)
    (rank : ℕ) :
    vectorEulerIteratedDerivative (rank+1) (jets 0) = rawEulerPolynomial jets (positiveEulerTerms rank) := by
  induction rank with
  | zero =>
      funext radius
      change radius • deriv (jets 0) radius = 1 • (radius^1 • jets 1 radius) + 0
      simp only [one_smul,add_zero,pow_one]
      rw [(derivative 0 radius).deriv]
  | succ rank previous =>
      change vectorEulerDerivative (vectorEulerIteratedDerivative (rank+1) (jets 0)) = _
      rw [previous]
      funext radius
      change radius • deriv (rawEulerPolynomial jets (positiveEulerTerms rank)) radius = _
      rw [(rawEulerPolynomial_hasDerivAt jets derivative _ radius).deriv]
      exact (rawEulerPolynomial_step jets (positiveEulerTerms rank) radius).symm

end Jets

theorem eulerProfilePolynomialStep_rank (rank : ℕ) (terms : List (ℕ × ℝ))
    (bound : ∀ term ∈ terms, term.1+1 ≤ rank+1) :
    ∀ term ∈ eulerProfilePolynomialStep terms, term.1+1 ≤ rank+2 := by
  induction terms with
  | nil => simp [eulerProfilePolynomialStep]
  | cons head terms previous =>
      intro term member
      change term ∈ (head.1,head.2*((head.1+1 : ℕ) : ℝ)) :: (head.1+1,head.2) :: eulerProfilePolynomialStep terms at member
      simp only [List.mem_cons] at member
      rcases member with same | same | tail
      · subst term; exact (bound head (List.mem_cons_self)).trans (by omega)
      · subst term; have := bound head (List.mem_cons_self); dsimp; omega
      · exact previous (fun term member => bound term (List.mem_cons_of_mem head member)) term tail

/-- Euler iteration never creates a raw radial rank beyond its total rank. -/
theorem positiveEulerTerms_rank (rank : ℕ) :
    ∀ term ∈ positiveEulerTerms rank, term.1+1 ≤ rank+1 := by
  induction rank with
  | zero =>
      intro term member
      have same : term = (0,1) := List.mem_singleton.mp member
      subst term
      exact le_rfl
  | succ rank previous => exact eulerProfilePolynomialStep_rank rank (positiveEulerTerms rank) previous

end Grad.OriginalCartesianTameEstimate
