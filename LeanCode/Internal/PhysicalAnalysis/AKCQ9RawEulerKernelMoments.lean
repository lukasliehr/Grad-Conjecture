import AKCQ8ActualRawEulerJetExpansion
import AHW12ScalarFactorsAndCofactorContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.ClosedJets Grad.SourceCollarDivision Grad.SourceBoundaryTrace

/-- The finite Euler expansion as a genuine full kernel, at the original
radius-dependent analytic width. -/
def rawEulerKernel {parameters : PhaseParameters} {source target : ℕ} (radius : RadialPoint)
    (kernels : ℕ → RadialKernel parameters radius source target) (terms : List (ℕ × ℝ)) :
    RadialKernel parameters radius source target :=
  List.rec (fullKernelSmul 0 (kernels 0)) (fun term _ previous => fullKernelAdd
    (fullKernelSmul ((term.2*radius.val^(term.1+1) : ℝ) : ℂ) (kernels (term.1+1))) previous) terms

def rawEulerMomentConstant (constants : ℕ → ℝ) (terms : List (ℕ × ℝ)) : ℝ :=
  List.rec 0 (fun term _ previous => |term.2| * constants (term.1+1) + previous) terms

theorem rawEulerMomentConstant_nonnegative (constants : ℕ → ℝ)
    (nonnegative : ∀ rank, 0 ≤ constants rank) (terms : List (ℕ × ℝ)) :
    0 ≤ rawEulerMomentConstant constants terms := by
  induction terms with
  | nil => exact le_rfl
  | cons term terms previous => exact add_nonneg (mul_nonneg (abs_nonneg _) (nonnegative _)) previous

theorem rawEulerKernel_entry {parameters : PhaseParameters} {source target : ℕ} (radius : RadialPoint)
    (kernels : ℕ → RadialKernel parameters radius source target) (terms : List (ℕ × ℝ))
    (shift input : ℤ × ℤ) :
    (rawEulerKernel radius kernels terms).entry shift input =
      rawEulerPolynomial (fun rank _ => (kernels rank).entry shift input) terms radius.val := by
  induction terms with
  | nil =>
      change (0 : ℂ) • (kernels 0).entry shift input = 0
      exact zero_smul ℂ ((kernels 0).entry shift input)
  | cons term terms previous =>
      change ((term.2*radius.val^(term.1+1) : ℝ) : ℂ) • (kernels (term.1+1)).entry shift input +
        (rawEulerKernel radius kernels terms).entry shift input =
          term.2 • (radius.val^(term.1+1) • (kernels (term.1+1)).entry shift input) +
            rawEulerPolynomial (fun rank _ => (kernels rank).entry shift input) terms radius.val
      rw [previous]
      congr 1
      ext value coordinate
      simp only [smul_apply,PiLp.smul_apply,Complex.real_smul]
      push_cast
      ring

/-- No rank is discarded: each term uses its original raw radial jet.
Powers of the actual radius cost at most one on the entire closed disk. -/
theorem rawEulerKernel_moment_bound {parameters : PhaseParameters} {source target : ℕ}
    (radius : RadialPoint) (kernels : ℕ → RadialKernel parameters radius source target)
    (terms : List (ℕ × ℝ)) (moment : ℕ) (constants : ℕ → ℝ) (size : ℝ)
    (bound : ∀ term ∈ terms, fullKernelMoment (radialKernelParameters parameters radius) moment
      (kernels (term.1+1)) ≤ constants (term.1+1)*size) :
    fullKernelMoment (radialKernelParameters parameters radius) moment (rawEulerKernel radius kernels terms) ≤
      rawEulerMomentConstant constants terms * size := by
  induction terms with
  | nil =>
      exact (fullKernelSmul_moment_le 0 (kernels 0) moment).trans_eq (by simp [rawEulerMomentConstant])
  | cons term terms previous =>
      have scalar : ‖((term.2*radius.val^(term.1+1) : ℝ) : ℂ)‖ ≤ |term.2| := by
        rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_pow,abs_of_nonneg radius.property.1]
        exact (mul_le_mul_of_nonneg_left (pow_le_one₀ radius.property.1 radius.property.2) (abs_nonneg _)).trans_eq (mul_one _)
      have first := (fullKernelSmul_moment_le ((term.2*radius.val^(term.1+1) : ℝ) : ℂ)
        (kernels (term.1+1)) moment).trans
        ((mul_le_mul_of_nonneg_right scalar (fullKernelMoment_nonnegative _ _ _)).trans
          (mul_le_mul_of_nonneg_left (bound term List.mem_cons_self) (abs_nonneg _)))
      have rest := previous (fun term member => bound term (List.mem_cons_of_mem _ member))
      exact (fullKernelAdd_moment_le _ moment _ _).trans
        ((add_le_add first rest).trans_eq (by dsimp only [rawEulerMomentConstant]; ring))

/-- Genuine entrywise Euler fidelity to any actual raw derivative tower. -/
theorem rawEulerKernel_actual {parameters : PhaseParameters} {source target : ℕ}
    (radius : RadialPoint) (kernels : ℕ → RadialKernel parameters radius source target)
    (jets : ℕ → ℝ → (ComplexEuclidean source →L[ℂ] ComplexEuclidean target))
    (derivative : ∀ rank point, HasDerivAt (jets rank) (jets (rank+1) point) point)
    (shift input : ℤ × ℤ) (same : ∀ rank, (kernels rank).entry shift input = jets rank radius.val)
    (rank : ℕ) :
    (rawEulerKernel radius kernels (positiveEulerTerms rank)).entry shift input =
      vectorEulerIteratedDerivative (rank+1) (jets 0) radius.val := by
  rw [rawEulerKernel_entry,vectorEulerIteratedDerivative_rawExpansion jets derivative rank]
  generalize positiveEulerTerms rank = terms
  induction terms with
  | nil => rfl
  | cons term terms previous =>
      change term.2 • rawEulerMonomial (fun rank _ => (kernels rank).entry shift input) (term.1+1) radius.val +
        rawEulerPolynomial (fun rank _ => (kernels rank).entry shift input) terms radius.val =
          term.2 • rawEulerMonomial jets (term.1+1) radius.val + rawEulerPolynomial jets terms radius.val
      rw [previous]
      simp only [rawEulerMonomial,same]

end Grad.OriginalCartesianTameEstimate
