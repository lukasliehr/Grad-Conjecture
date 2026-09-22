import AKDA6OrderedInverseJointMomentAllocation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set
namespace Grad.OriginalCartesianTameEstimate

section Vector
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual Euler operator on a closed collar uses the one-sided
derivative at its boundary. No extension of the inverse is chosen. -/
def vectorEulerWithinIteratedDerivative (domain : Set ℝ) (rank : ℕ) (field : ℝ → E) : ℝ → E :=
  Nat.rec field (fun _ previous => fun radius => radius • derivWithin previous domain radius) rank

theorem vectorEulerWithinIteratedDerivative_tower (domain : Set ℝ)
    (unique : UniqueDiffOn ℝ domain) (nonzero : ∀ radius ∈ domain, radius ≠ 0)
    (jets : ℕ → ℝ → E)
    (derivative : ∀ rank radius, radius ∈ domain →
      HasDerivWithinAt (jets rank) (radius⁻¹ • jets (rank+1) radius) domain radius)
    (rank : ℕ) : EqOn (vectorEulerWithinIteratedDerivative domain rank (jets 0)) (jets rank) domain := by
  induction rank with
  | zero => intro radius _; rfl
  | succ rank previous =>
      intro radius inside
      change radius • derivWithin (vectorEulerWithinIteratedDerivative domain rank (jets 0)) domain radius = _
      rw [derivWithin_congr previous (previous inside), (derivative rank radius inside).derivWithin (unique radius inside)]
      exact smul_inv_smul₀ (nonzero radius inside) _

theorem rawEulerMonomial_hasDerivWithinAt (domain : Set ℝ) (jets : ℕ → ℝ → E)
    (radius : ℝ)
    (derivative : ∀ rank, HasDerivWithinAt (jets rank) (jets (rank+1) radius) domain radius)
    (rank : ℕ) :
    HasDerivWithinAt (rawEulerMonomial jets rank) (rawEulerMonomialDerivative jets rank radius) domain radius := by
  change HasDerivWithinAt (fun point => point^rank • jets rank point) _ domain radius
  apply ((((hasDerivAt_id radius).pow rank).hasDerivWithinAt).smul (derivative rank)).congr_deriv
  simp only [rawEulerMonomialDerivative,Pi.pow_apply,id_eq,mul_one]
  exact add_comm _ _

theorem rawEulerPolynomial_hasDerivWithinAt (domain : Set ℝ) (jets : ℕ → ℝ → E)
    (radius : ℝ)
    (derivative : ∀ rank, HasDerivWithinAt (jets rank) (jets (rank+1) radius) domain radius)
    (terms : List (ℕ × ℝ)) :
    HasDerivWithinAt (rawEulerPolynomial jets terms) (rawEulerPolynomialDerivative jets terms radius) domain radius := by
  induction terms with
  | nil => exact hasDerivWithinAt_const radius domain 0
  | cons term terms previous =>
      change HasDerivWithinAt
        (fun point => term.2 • rawEulerMonomial jets (term.1+1) point + rawEulerPolynomial jets terms point)
        (term.2 • rawEulerMonomialDerivative jets (term.1+1) radius + rawEulerPolynomialDerivative jets terms radius) domain radius
      simpa only [Pi.add_def,Pi.smul_apply] using
        ((rawEulerMonomial_hasDerivWithinAt domain jets radius derivative (term.1+1)).const_smul term.2).add previous

/-- The finite raw-jet expansion includes the unchanged order-zero field. -/
def actualRawEulerJets (jets : ℕ → ℝ → E) (rank : ℕ) : ℝ → E :=
  Nat.casesOn rank (jets 0) (fun order => rawEulerPolynomial jets (positiveEulerTerms order))

theorem actualRawEulerJets_hasDerivWithinAt (domain : Set ℝ) (jets : ℕ → ℝ → E)
    (radius : ℝ) (nonzero : radius ≠ 0)
    (derivative : ∀ rank, HasDerivWithinAt (jets rank) (jets (rank+1) radius) domain radius)
    (rank : ℕ) :
    HasDerivWithinAt (actualRawEulerJets jets rank)
      (radius⁻¹ • actualRawEulerJets jets (rank+1) radius) domain radius := by
  cases rank with
  | zero =>
      change HasDerivWithinAt (jets 0) (radius⁻¹ • (1 • (radius^1 • jets 1 radius)+0)) domain radius
      simpa only [pow_one,one_smul,add_zero,inv_smul_smul₀ nonzero] using derivative 0
  | succ rank =>
      change HasDerivWithinAt (rawEulerPolynomial jets (positiveEulerTerms rank))
        (radius⁻¹ • rawEulerPolynomial jets (eulerProfilePolynomialStep (positiveEulerTerms rank)) radius) domain radius
      rw [rawEulerPolynomial_step,inv_smul_smul₀ nonzero]
      exact rawEulerPolynomial_hasDerivWithinAt domain jets radius derivative _

theorem actualRawEulerJets_fidelity (domain : Set ℝ) (unique : UniqueDiffOn ℝ domain)
    (nonzero : ∀ radius ∈ domain, radius ≠ 0) (jets : ℕ → ℝ → E)
    (derivative : ∀ rank radius, radius ∈ domain → HasDerivWithinAt (jets rank) (jets (rank+1) radius) domain radius)
    (rank : ℕ) :
    EqOn (vectorEulerWithinIteratedDerivative domain rank (jets 0)) (actualRawEulerJets jets rank) domain :=
  vectorEulerWithinIteratedDerivative_tower domain unique nonzero (actualRawEulerJets jets)
    (fun order radius inside => actualRawEulerJets_hasDerivWithinAt domain jets radius (nonzero radius inside)
      (fun raw => derivative raw radius inside) order) rank

end Vector

section Inverse
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

/-- The ordered expression is the genuine iterated Euler derivative of
the SAME inverse on the closed domain, including its one-sided boundary. -/
theorem inverseEulerExpression_fidelity (domain : Set ℝ) (unique : UniqueDiffOn ℝ domain)
    (nonzero : ∀ radius ∈ domain, radius ≠ 0) (inverse : ℝ → R) (forward : ℕ → ℝ → R)
    (inverseDerivative : ∀ radius, radius ∈ domain → HasDerivWithinAt inverse
      (radius⁻¹ • (-(inverse radius*(forward 1 radius*inverse radius)))) domain radius)
    (forwardDerivative : ∀ rank radius, radius ∈ domain → HasDerivWithinAt (forward (rank+1))
      (radius⁻¹ • forward (rank+2) radius) domain radius) (rank : ℕ) :
    EqOn (vectorEulerWithinIteratedDerivative domain rank inverse)
      (fun radius => inverseEulerExprValue (inverse radius) (fun order => forward order radius) (inverseEulerExpression rank)) domain := by
  let jets := fun order radius => inverseEulerExprValue (inverse radius) (fun raw => forward raw radius) (inverseEulerExpression order)
  exact vectorEulerWithinIteratedDerivative_tower domain unique nonzero jets
    (fun order radius inside => inverseEulerExpr_hasDerivWithinAt domain inverse forward radius
      (inverseDerivative radius inside) (fun raw => forwardDerivative raw radius inside) (inverseEulerExpression order)) rank

end Inverse

end Grad.OriginalCartesianTameEstimate
