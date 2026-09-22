import AKCQ1SharpEulerProfileMonomials

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.AnalyticWeights.Higher

/-- The actual Euler operator r times the ordinary radial derivative. -/
def eulerDerivative (field : ℝ → ℝ) (point : ℝ) : ℝ := point * deriv field point

def eulerIteratedDerivative (order : ℕ) (field : ℝ → ℝ) : ℝ → ℝ :=
  Nat.rec field (fun _ previous => eulerDerivative previous) order

/-- List indices represent strictly positive monomial ranks. -/
def eulerProfilePolynomial (terms : List (ℕ × ℝ)) (point : ℝ) : ℝ :=
  List.rec 0 (fun term _ previous => term.2 * eulerRayMonomial (term.1+1) point + previous) terms

def eulerProfilePolynomialDerivative (terms : List (ℕ × ℝ)) (point : ℝ) : ℝ :=
  List.rec 0 (fun term _ previous => term.2 * eulerRayMonomialDerivative (term.1+1) point + previous) terms

def eulerProfileValueConstant (terms : List (ℕ × ℝ)) : ℝ :=
  List.rec 0 (fun term _ previous => |term.2| * profileConstant (term.1+1) + previous) terms

def eulerProfileDerivativeConstant (terms : List (ℕ × ℝ)) : ℝ :=
  List.rec 0 (fun term _ previous => |term.2| * spectralConstant (term.1+1) + previous) terms

theorem eulerProfileValueConstant_nonnegative (terms : List (ℕ × ℝ)) :
    0 ≤ eulerProfileValueConstant terms := by
  induction terms with
  | nil => exact le_rfl
  | cons term terms previous =>
      exact add_nonneg (mul_nonneg (abs_nonneg _) (profileConstant_nonnegative _)) previous

theorem eulerProfileDerivativeConstant_nonnegative (terms : List (ℕ × ℝ)) :
    0 ≤ eulerProfileDerivativeConstant terms := by
  induction terms with
  | nil => exact le_rfl
  | cons term terms previous =>
      exact add_nonneg (mul_nonneg (abs_nonneg _) (spectralConstant_nonnegative _)) previous

theorem eulerProfilePolynomial_hasDerivAt (terms : List (ℕ × ℝ)) (point : ℝ) :
    HasDerivAt (eulerProfilePolynomial terms) (eulerProfilePolynomialDerivative terms point) point := by
  induction terms with
  | nil => exact hasDerivAt_const point 0
  | cons term terms previous =>
      change HasDerivAt (fun location => term.2 * eulerRayMonomial (term.1+1) location +
        eulerProfilePolynomial terms location)
        (term.2 * eulerRayMonomialDerivative (term.1+1) point + eulerProfilePolynomialDerivative terms point) point
      simpa only [Pi.add_def,Pi.mul_def] using
        ((eulerRayMonomial_hasDerivAt (term.1+1) point).const_mul term.2).add previous

theorem eulerProfilePolynomial_bound (terms : List (ℕ × ℝ)) (point : ℝ) :
    ‖eulerProfilePolynomial terms point‖ ≤ eulerProfileValueConstant terms * |point| := by
  induction terms with
  | nil => simp only [eulerProfilePolynomial,eulerProfileValueConstant,norm_zero,zero_mul,le_refl]
  | cons term terms previous =>
      calc
        _ ≤ ‖term.2 * eulerRayMonomial (term.1+1) point‖ + ‖eulerProfilePolynomial terms point‖ := norm_add_le _ _
        _ = |term.2| * ‖eulerRayMonomial (term.1+1) point‖ + ‖eulerProfilePolynomial terms point‖ := by
          rw [norm_mul,Real.norm_eq_abs]
        _ ≤ |term.2| * (profileConstant (term.1+1) * |point|) + eulerProfileValueConstant terms * |point| :=
          add_le_add (mul_le_mul_of_nonneg_left (eulerRayMonomial_bound (term.1+1) (by omega) point)
            (abs_nonneg _)) previous
        _ = _ := by dsimp only [eulerProfileValueConstant]; ring

theorem eulerProfilePolynomialDerivative_bound (terms : List (ℕ × ℝ)) (point : ℝ) :
    ‖eulerProfilePolynomialDerivative terms point‖ ≤ eulerProfileDerivativeConstant terms := by
  induction terms with
  | nil => simp only [eulerProfilePolynomialDerivative,eulerProfileDerivativeConstant,norm_zero,le_refl]
  | cons term terms previous =>
      calc
        _ ≤ ‖term.2 * eulerRayMonomialDerivative (term.1+1) point‖ + ‖eulerProfilePolynomialDerivative terms point‖ := norm_add_le _ _
        _ = |term.2| * ‖eulerRayMonomialDerivative (term.1+1) point‖ + ‖eulerProfilePolynomialDerivative terms point‖ := by
          rw [norm_mul,Real.norm_eq_abs]
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left
          (eulerRayMonomialDerivative_bound (term.1+1) (by omega) point) (abs_nonneg _)) previous

/-- Applying Euler preserves the finite positive-rank monomial list. -/
def eulerProfilePolynomialStep (terms : List (ℕ × ℝ)) : List (ℕ × ℝ) :=
  List.rec [] (fun term _ previous =>
    (term.1,term.2*(term.1+1 : ℕ)) :: (term.1+1,term.2) :: previous) terms

theorem eulerRayMonomial_euler (rank : ℕ) (point : ℝ) :
    point * eulerRayMonomialDerivative (rank+1) point =
      ((rank+1 : ℕ) : ℝ) * eulerRayMonomial (rank+1) point + eulerRayMonomial (rank+2) point := by
  simp only [eulerRayMonomialDerivative,eulerRayMonomial,Nat.add_sub_cancel,pow_succ]
  ring

theorem eulerProfilePolynomial_step (terms : List (ℕ × ℝ)) (point : ℝ) :
    eulerProfilePolynomial (eulerProfilePolynomialStep terms) point =
      point * eulerProfilePolynomialDerivative terms point := by
  induction terms with
  | nil => simp only [eulerProfilePolynomialStep,eulerProfilePolynomial,eulerProfilePolynomialDerivative,mul_zero]
  | cons term terms previous =>
      change (term.2*((term.1+1 : ℕ) : ℝ)) * eulerRayMonomial (term.1+1) point +
        (term.2 * eulerRayMonomial (term.1+2) point + eulerProfilePolynomial (eulerProfilePolynomialStep terms) point) =
        point * (term.2 * eulerRayMonomialDerivative (term.1+1) point + eulerProfilePolynomialDerivative terms point)
      rw [previous]
      calc
        _ = term.2 * (((term.1+1 : ℕ) : ℝ) * eulerRayMonomial (term.1+1) point +
            eulerRayMonomial (term.1+2) point) + point * eulerProfilePolynomialDerivative terms point := by ring
        _ = term.2 * (point * eulerRayMonomialDerivative (term.1+1) point) +
            point * eulerProfilePolynomialDerivative terms point := by rw [eulerRayMonomial_euler]
        _ = _ := by ring

def positiveEulerTerms (order : ℕ) : List (ℕ × ℝ) :=
  Nat.rec [(0,1)] (fun _ previous => eulerProfilePolynomialStep previous) order

def positiveEulerProfile (order : ℕ) : ℝ → ℝ := eulerProfilePolynomial (positiveEulerTerms order)

theorem positiveEulerProfile_succ (order : ℕ) :
    positiveEulerProfile (order+1) = eulerDerivative (positiveEulerProfile order) := by
  funext point
  change eulerProfilePolynomial (eulerProfilePolynomialStep (positiveEulerTerms order)) point =
    point * deriv (eulerProfilePolynomial (positiveEulerTerms order)) point
  rw [(eulerProfilePolynomial_hasDerivAt _ point).deriv,eulerProfilePolynomial_step]

theorem eulerIteratedDerivative_profile (order : ℕ) :
    eulerIteratedDerivative (order+1) eulerProfileRay = positiveEulerProfile order := by
  induction order with
  | zero =>
      funext point
      change point * deriv eulerProfileRay point = 1 * (point^1 * iteratedDeriv 1 eulerProfileRay point) + 0
      simp only [one_mul,pow_one,iteratedDeriv_one,add_zero]
  | succ order previous =>
      change eulerDerivative (eulerIteratedDerivative (order+1) eulerProfileRay) = positiveEulerProfile (order+1)
      rw [previous,positiveEulerProfile_succ]

end Grad.OriginalCartesianTameEstimate
