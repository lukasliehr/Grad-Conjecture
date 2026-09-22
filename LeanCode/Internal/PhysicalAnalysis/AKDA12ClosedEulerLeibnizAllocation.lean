import AKDA11OriginalInverseJointEulerMoments

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate

/-- Ordered Leibniz allocations keep both derivative ranks. Repeated
terms retain the exact integer multiplicity without merging factors. -/
def eulerLeibnizStep (terms : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  List.rec [] (fun term _ previous => (term.1+1,term.2)::(term.1,term.2+1)::previous) terms

def eulerLeibnizTerms (rank : ℕ) : List (ℕ × ℕ) :=
  Nat.rec [(0,0)] (fun _ previous => eulerLeibnizStep previous) rank

theorem eulerLeibnizStep_rank (rank : ℕ) (terms : List (ℕ × ℕ))
    (allocated : ∀ term ∈ terms, term.1+term.2 = rank) :
    ∀ term ∈ eulerLeibnizStep terms, term.1+term.2 = rank+1 := by
  induction terms with
  | nil => simp [eulerLeibnizStep]
  | cons head terms previous =>
      intro term member
      change term ∈ (head.1+1,head.2)::(head.1,head.2+1)::eulerLeibnizStep terms at member
      simp only [List.mem_cons] at member
      rcases member with same | same | tail
      · subst term; have := allocated head List.mem_cons_self; dsimp; omega
      · subst term; have := allocated head List.mem_cons_self; dsimp; omega
      · exact previous (fun term member => allocated term (List.mem_cons_of_mem head member)) term tail

theorem eulerLeibnizTerms_rank (rank : ℕ) : ∀ term ∈ eulerLeibnizTerms rank, term.1+term.2 = rank := by
  induction rank with
  | zero =>
      intro term member
      have same : term = (0,0) := List.mem_singleton.mp member
      subst term; rfl
  | succ rank previous => exact eulerLeibnizStep_rank rank _ previous

def eulerAllocationSum (values : ℕ → ℕ → ℝ) (terms : List (ℕ × ℕ)) : ℝ :=
  List.rec 0 (fun term _ previous => values term.1 term.2+previous) terms

theorem eulerAllocationSum_nonnegative (values : ℕ → ℕ → ℝ)
    (nonnegative : ∀ first second, 0 ≤ values first second) (terms : List (ℕ × ℕ)) :
    0 ≤ eulerAllocationSum values terms := by
  induction terms with
  | nil => exact le_rfl
  | cons term terms previous => exact add_nonneg (nonnegative _ _) previous

section Vector
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def scalarEulerPolynomial (scalar : ℕ → ℝ → ℝ) (vector : ℕ → ℝ → E)
    (terms : List (ℕ × ℕ)) (radius : ℝ) : E :=
  List.rec 0 (fun term _ previous => scalar term.1 radius • vector term.2 radius+previous) terms

theorem scalarEulerPolynomial_hasDerivWithinAt (domain : Set ℝ)
    (scalar : ℕ → ℝ → ℝ) (vector : ℕ → ℝ → E) (radius : ℝ)
    (scalarDerivative : ∀ rank, HasDerivWithinAt (scalar rank) (radius⁻¹ • scalar (rank+1) radius) domain radius)
    (vectorDerivative : ∀ rank, HasDerivWithinAt (vector rank) (radius⁻¹ • vector (rank+1) radius) domain radius)
    (terms : List (ℕ × ℕ)) :
    HasDerivWithinAt (scalarEulerPolynomial scalar vector terms)
      (radius⁻¹ • scalarEulerPolynomial scalar vector (eulerLeibnizStep terms) radius) domain radius := by
  induction terms with
  | nil =>
      change HasDerivWithinAt (fun _ => (0 : E)) (radius⁻¹ • 0) domain radius
      rw [smul_zero]
      exact hasDerivWithinAt_const radius domain 0
  | cons term terms previous =>
      change HasDerivWithinAt (fun point => scalar term.1 point • vector term.2 point+scalarEulerPolynomial scalar vector terms point)
        (radius⁻¹ • (scalar (term.1+1) radius • vector term.2 radius+
          (scalar term.1 radius • vector (term.2+1) radius+scalarEulerPolynomial scalar vector (eulerLeibnizStep terms) radius))) domain radius
      apply (((scalarDerivative term.1).smul (vectorDerivative term.2)).add previous).congr_deriv
      simp only [smul_add,smul_smul,smul_eq_mul]
      module

/-- Genuine Leibniz expansion for closed-collar Euler derivatives from
the actual derivative towers. It includes both one-sided endpoints. -/
theorem scalarEulerPolynomial_fidelity (domain : Set ℝ) (unique : UniqueDiffOn ℝ domain)
    (nonzero : ∀ radius ∈ domain, radius ≠ 0)
    (scalar : ℕ → ℝ → ℝ) (vector : ℕ → ℝ → E)
    (scalarDerivative : ∀ rank radius, radius ∈ domain →
      HasDerivWithinAt (scalar rank) (radius⁻¹ • scalar (rank+1) radius) domain radius)
    (vectorDerivative : ∀ rank radius, radius ∈ domain →
      HasDerivWithinAt (vector rank) (radius⁻¹ • vector (rank+1) radius) domain radius)
    (rank : ℕ) (radius : ℝ) (inside : radius ∈ domain) :
    vectorEulerWithinIteratedDerivative domain rank (fun point => scalar 0 point • vector 0 point) radius =
      scalarEulerPolynomial scalar vector (eulerLeibnizTerms rank) radius := by
  have actual := vectorEulerWithinIteratedDerivative_tower domain unique nonzero
    (fun order => scalarEulerPolynomial scalar vector (eulerLeibnizTerms order))
    (fun order radius member => scalarEulerPolynomial_hasDerivWithinAt domain scalar vector radius
      (fun raw => scalarDerivative raw radius member) (fun raw => vectorDerivative raw radius member) (eulerLeibnizTerms order)) rank inside
  have initial : scalarEulerPolynomial scalar vector (eulerLeibnizTerms 0) = (fun point => scalar 0 point • vector 0 point) := by
    funext point
    change scalar 0 point • vector 0 point+0 = _
    exact add_zero _
  rwa [initial] at actual

theorem scalarEulerPolynomial_norm (scalar : ℕ → ℝ → ℝ) (vector : ℕ → ℝ → E)
    (terms : List (ℕ × ℕ)) (radius : ℝ) :
    ‖scalarEulerPolynomial scalar vector terms radius‖ ≤
      eulerAllocationSum (fun first second => ‖scalar first radius‖*‖vector second radius‖) terms := by
  induction terms with
  | nil => exact le_of_eq (norm_zero)
  | cons term terms previous =>
      change ‖scalar term.1 radius • vector term.2 radius+scalarEulerPolynomial scalar vector terms radius‖ ≤
        ‖scalar term.1 radius‖*‖vector term.2 radius‖+_
      exact (norm_add_le _ _).trans (add_le_add (le_of_eq (norm_smul _ _)) previous)

end Vector

theorem actualScalarEulerJets_hasDerivWithinAt (domain : Set ℝ) (field : ℝ → ℝ)
    (smooth : ContDiff ℝ ∞ field) (rank : ℕ) (radius : ℝ) (nonzero : radius ≠ 0) :
    HasDerivWithinAt (eulerIteratedDerivative rank field)
      (radius⁻¹ • eulerIteratedDerivative (rank+1) field radius) domain radius := by
  have actual := (((eulerIteratedDerivative_smooth field smooth rank).differentiable (by simp) radius).hasDerivAt).hasDerivWithinAt (s := domain)
  change HasDerivWithinAt (eulerIteratedDerivative rank field)
    (radius⁻¹ * (radius*deriv (eulerIteratedDerivative rank field) radius)) domain radius
  simpa only [inv_mul_cancel_left₀ nonzero] using actual

end Grad.OriginalCartesianTameEstimate
