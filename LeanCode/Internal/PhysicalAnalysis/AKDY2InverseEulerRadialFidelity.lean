import AKDY1InverseEulerPolynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set
namespace Grad.OriginalRadialRecovery

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The radial inverse polynomial retains the exact inverse-radius power. -/
def inverseRadialJet (jets : ℕ → ℝ → E) (rank : ℕ) (radius : ℝ) : E :=
  (radius⁻¹)^rank • eulerCombination jets (inverseEulerTerms rank) radius

theorem inversePower_hasDerivWithinAt (domain : Set ℝ) (rank : ℕ)
    (radius : ℝ) (nonzero : radius≠0) :
    HasDerivWithinAt (fun point : ℝ => (point⁻¹)^rank)
      (-(rank:ℝ)*(radius⁻¹)^(rank+1)) domain radius := by
  cases rank with
  | zero => simpa using hasDerivWithinAt_const radius domain (1:ℝ)
  | succ rank =>
      apply ((hasDerivWithinAt_inv nonzero domain).pow (rank+1)).congr_deriv
      simp only [Nat.add_sub_cancel,inv_pow,pow_succ]
      ring

theorem inverseRadialJet_hasDerivWithinAt (domain : Set ℝ) (jets : ℕ → ℝ → E)
    (radius : ℝ) (nonzero : radius≠0)
    (derivative : ∀ order,HasDerivWithinAt (jets order)
      (radius⁻¹ • jets (order+1) radius) domain radius) (rank : ℕ) :
    HasDerivWithinAt (inverseRadialJet jets rank)
      (inverseRadialJet jets (rank+1) radius) domain radius := by
  have result := (inversePower_hasDerivWithinAt domain rank radius nonzero).smul
    (eulerCombination_hasDerivWithinAt domain jets radius derivative (inverseEulerTerms rank))
  apply result.congr_deriv
  change (radius⁻¹)^rank • (radius⁻¹ • eulerCombination (fun order => jets (order+1)) (inverseEulerTerms rank) radius)+
    (-(rank:ℝ)*(radius⁻¹)^(rank+1)) • eulerCombination jets (inverseEulerTerms rank) radius = _
  change _ = (radius⁻¹)^(rank+1) • eulerCombination jets
    (inverseEulerStep rank (inverseEulerTerms rank)) radius
  rw [eulerCombination_step]
  simp only [smul_sub,smul_smul,pow_succ]
  module

/-- Finite inverse Euler polynomials equal the actual ordinary radial
jets within the SAME domain, including its one-sided boundary. -/
theorem inverseRadialJet_fidelity (domain : Set ℝ) (unique : UniqueDiffOn ℝ domain)
    (nonzero : ∀ radius ∈ domain,radius≠0) (jets : ℕ → ℝ → E)
    (derivative : ∀ order radius,radius∈domain → HasDerivWithinAt (jets order)
      (radius⁻¹ • jets (order+1) radius) domain radius) (rank : ℕ) :
    EqOn (iteratedDerivWithin rank (jets 0) domain) (inverseRadialJet jets rank) domain := by
  induction rank with
  | zero =>
      intro radius _
      change jets 0 radius = 1 • ((1:ℝ) • jets 0 radius+0)
      simp only [one_smul,add_zero]
  | succ rank previous =>
      intro radius inside
      rw [iteratedDerivWithin_succ]
      rw [derivWithin_congr previous (previous inside)]
      exact (inverseRadialJet_hasDerivWithinAt domain jets radius (nonzero radius inside)
        (fun order => derivative order radius inside) rank).derivWithin (unique radius inside)

end Grad.OriginalRadialRecovery
