import AKDA7ClosedCollarEulerFidelity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.AnnularRadialSmoothness

theorem polynomialKernelAction_smul {source target : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (scalar : ℂ) (kernel : FullTwoFrequencyKernel parameters source target) :
    polynomialKernelAction parameters power (fullKernelSmul scalar kernel) =
      scalar • polynomialKernelAction parameters power kernel := by
  apply ContinuousLinearMap.ext
  intro field
  apply lp.ext
  funext mode
  apply (polynomialKernelAction_coefficient parameters power (fullKernelSmul scalar kernel) field mode).unique
  have scaled := (polynomialKernelAction_coefficient parameters power kernel field mode).const_smul scalar
  change HasSum (fun shift => (polynomialWeightRatio power shift mode : ℂ) •
    (scalar • kernel.entry shift (twoFrequencyTranslation shift mode) (field (twoFrequencyTranslation shift mode))))
    (scalar • polynomialKernelAction parameters power kernel field mode)
  exact scaled.congr_fun (fun shift => smul_comm _ _ _)

theorem polynomialKernelAction_real_smul {source target : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (scalar : ℝ) (kernel : FullTwoFrequencyKernel parameters source target) :
    polynomialKernelAction parameters power (fullKernelSmul (scalar : ℂ) kernel) =
      scalar • polynomialKernelAction parameters power kernel := by
  rw [polynomialKernelAction_smul]
  ext field mode coordinate
  change (scalar : ℂ) * (polynomialKernelAction parameters power kernel field mode coordinate) =
    (scalar : ℂ) * (polynomialKernelAction parameters power kernel field mode coordinate)
  rfl

theorem rawEulerPolynomial_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (first second : ℕ → ℝ → E) (terms : List (ℕ × ℝ)) (radius : ℝ)
    (same : ∀ rank, first rank radius = second rank radius) :
    rawEulerPolynomial first terms radius = rawEulerPolynomial second terms radius := by
  induction terms with
  | nil => rfl
  | cons term terms previous =>
      change term.2 • (radius^(term.1+1) • first (term.1+1) radius) + rawEulerPolynomial first terms radius =
        term.2 • (radius^(term.1+1) • second (term.1+1) radius) + rawEulerPolynomial second terms radius
      rw [same,previous]

/-- The finite Euler kernel represents precisely the original operator
Euler polynomial, without phase weights inserted into the algebra. -/
theorem rawEulerKernel_action {parameters : PhaseParameters} {source target : ℕ} (radius : RadialPoint)
    (kernels : ℕ → RadialKernel parameters radius source target) (terms : List (ℕ × ℝ)) :
    polynomialKernelAction (radialKernelParameters parameters radius) 0 (rawEulerKernel radius kernels terms) =
      rawEulerPolynomial (fun rank _ => polynomialKernelAction (radialKernelParameters parameters radius) 0 (kernels rank)) terms radius.val := by
  induction terms with
  | nil =>
      change polynomialKernelAction _ 0 (fullKernelSmul 0 (kernels 0)) = 0
      rw [polynomialKernelAction_smul,zero_smul]
  | cons term terms previous =>
      change polynomialKernelAction _ 0 (fullKernelAdd
        (fullKernelSmul ((term.2*radius.val^(term.1+1) : ℝ) : ℂ) (kernels (term.1+1)))
        (rawEulerKernel radius kernels terms)) = _
      rw [polynomialKernelAction_add,polynomialKernelAction_real_smul,previous]
      change (term.2*radius.val^(term.1+1)) • polynomialKernelAction _ 0 (kernels (term.1+1)) + _ =
        term.2 • (radius.val^(term.1+1) • polynomialKernelAction _ 0 (kernels (term.1+1))) + _
      rw [smul_smul]
      rfl

def actualRawEulerKernel {parameters : PhaseParameters} {source target : ℕ} (radius : RadialPoint)
    (kernels : ℕ → RadialKernel parameters radius source target) (rank : ℕ) :
    RadialKernel parameters radius source target :=
  Nat.casesOn rank (kernels 0) (fun order => rawEulerKernel radius kernels (positiveEulerTerms order))

theorem actualRawEulerKernel_action {parameters : PhaseParameters} {source target : ℕ} (radius : RadialPoint)
    (kernels : ℕ → RadialKernel parameters radius source target) (rank : ℕ) :
    polynomialKernelAction (radialKernelParameters parameters radius) 0 (actualRawEulerKernel radius kernels rank) =
      actualRawEulerJets (fun order _ => polynomialKernelAction (radialKernelParameters parameters radius) 0 (kernels order)) rank radius.val := by
  cases rank with
  | zero => rfl
  | succ rank => exact rawEulerKernel_action radius kernels _

theorem actualRawEulerKernel_collar_action {source target : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernels : ℕ → (radius : RadialPoint) → RadialKernel parameters radius source target)
    (rank : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    polynomialKernelAction (radialKernelParameters parameters (collarRadius lower positive bounded radius)) 0
      (actualRawEulerKernel (collarRadius lower positive bounded radius) (fun order => kernels order (collarRadius lower positive bounded radius)) rank) =
      actualRawEulerJets (fun order => radialPolynomialAction parameters lower positive bounded (kernels order) 0) rank radius := by
  rw [actualRawEulerKernel_action]
  cases rank with
  | zero => rfl
  | succ rank =>
      change rawEulerPolynomial _ _ (collarRadius lower positive bounded radius).val = rawEulerPolynomial _ _ radius
      rw [collarRadius_literal lower positive bounded radius inside]
      exact rawEulerPolynomial_congr _ _ _ radius (fun _ => rfl)

end Grad.OriginalCartesianTameEstimate
