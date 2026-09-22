import AIX1ActualDisplacementCharacters
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal ContDiff
namespace Grad.AnnularOrbitGenerators
open Grad.CartesianState Grad.FourierGrade Grad.AnnularKernelOrbit

section LinearExtraction
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Bounded coefficient extraction commutes with all derivatives in the
complete ambient norm. Smoothness is required, not inferred from isometry. -/
theorem coefficient_iteratedDeriv (coefficient : E →L[ℝ] F) (orbit : ℝ → E)
    (smooth : ContDiff ℝ ∞ orbit) (order : ℕ) (time : ℝ) :
    coefficient (iteratedDeriv order orbit time) =
      iteratedDeriv order (fun parameter => coefficient (orbit parameter)) time := by
  induction order generalizing time with
  | zero => rfl
  | succ order induction =>
    have same : (fun parameter => coefficient (iteratedDeriv order orbit parameter)) =
        iteratedDeriv order (fun parameter => coefficient (orbit parameter)) := funext induction
    rw [iteratedDeriv_succ, iteratedDeriv_succ, ← same]
    exact (coefficient.hasFDerivAt.comp_hasDerivAt time
      ((smooth.differentiable_iteratedDeriv order (by exact_mod_cast (show (order : ℕ∞) < ⊤ from WithTop.coe_lt_top order))) time).hasDerivAt).deriv.symm

end LinearExtraction

section Character
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

theorem cellExponential_hasDerivAt (mode : ℤ) (time : ℝ) :
    HasDerivAt (cellExponential mode) ((Complex.I * (mode : ℂ)) * cellExponential mode time) time := by
  have derivative := (cellExponential_hasFDerivAt mode time).hasDerivAt
  simpa [cellExponentialDerivative, mul_comm] using derivative

theorem characterVector_iteratedDeriv (mode : ℤ) (value : F) (order : ℕ) (time : ℝ) :
    iteratedDeriv order (fun parameter => cellExponential mode parameter • value) time =
      (Complex.I * (mode : ℂ)) ^ order • (cellExponential mode time • value) := by
  induction order generalizing time with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_smul]
  | succ order induction =>
    have same : iteratedDeriv order (fun parameter => cellExponential mode parameter • value) =
        fun parameter => (Complex.I * (mode : ℂ)) ^ order • (cellExponential mode parameter • value) := funext induction
    rw [iteratedDeriv_succ, same]
    have derivative := ((cellExponential_hasDerivAt mode time).smul_const value).const_smul
      ((Complex.I * (mode : ℂ)) ^ order)
    have result := derivative.deriv
    change deriv (fun parameter => (Complex.I * (mode : ℂ)) ^ order • (cellExponential mode parameter • value)) time = _ at result
    simpa only [smul_smul, pow_succ, mul_assoc] using result

end Character

section GenuineGenerator
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

/-- A smooth orbit in the genuine complete carrier supplies its actual
Fourier-generator powers as elements of that same carrier. -/
theorem smoothCharacterOrbit_coefficient (coefficient : E →L[ℂ] F) (orbit : ℝ → E)
    (smooth : ContDiff ℝ ∞ orbit) (mode : ℤ) (value : F)
    (character : ∀ time, coefficient (orbit time) = cellExponential mode time • value)
    (order : ℕ) (time : ℝ) :
    coefficient (iteratedDeriv order orbit time) =
      (Complex.I * (mode : ℂ)) ^ order • (cellExponential mode time • value) := by
  have extracted := coefficient_iteratedDeriv (coefficient.restrictScalars ℝ) orbit smooth order time
  have same : (fun parameter => (coefficient.restrictScalars ℝ) (orbit parameter)) =
      fun parameter => cellExponential mode parameter • value := funext character
  rw [same, characterVector_iteratedDeriv] at extracted
  exact extracted

theorem smoothCharacterOrbit_generator (coefficient : E →L[ℂ] F) (orbit : ℝ → E)
    (smooth : ContDiff ℝ ∞ orbit) (mode : ℤ) (value : F)
    (character : ∀ time, coefficient (orbit time) = cellExponential mode time • value)
    (order : ℕ) :
    coefficient (iteratedDeriv order orbit 0) = (Complex.I * (mode : ℂ)) ^ order • value := by
  have actual := smoothCharacterOrbit_coefficient coefficient orbit smooth mode value character order 0
  simpa only [cellExponential, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul] using actual

end GenuineGenerator

end Grad.AnnularOrbitGenerators
