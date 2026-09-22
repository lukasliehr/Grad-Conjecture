import AKCQ2FiniteEulerProfileExpansion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.PhaseAlgebra Grad.AnnularWeightedSmoothness
open Grad.AnalyticWeights.Higher

theorem eulerProfilePolynomial_difference (terms : List (ℕ × ℝ)) (first second : ℝ) :
    ‖eulerProfilePolynomial terms second - eulerProfilePolynomial terms first‖ ≤
      eulerProfileDerivativeConstant terms * |second-first| := by
  have ordered (first second : ℝ) (before : first ≤ second) :
      ‖eulerProfilePolynomial terms second - eulerProfilePolynomial terms first‖ ≤
        eulerProfileDerivativeConstant terms * (second-first) := by
    exact norm_image_sub_le_of_norm_deriv_le_segment'
      (fun point _ => (eulerProfilePolynomial_hasDerivAt terms point).hasDerivWithinAt)
      (fun point _ => eulerProfilePolynomialDerivative_bound terms point) second ⟨before,le_rfl⟩
  rcases le_total first second with before | before
  · simpa only [abs_of_nonneg (sub_nonneg.mpr before)] using ordered first second before
  · rw [norm_sub_rev,abs_sub_comm]
    simpa only [abs_of_nonneg (sub_nonneg.mpr before)] using ordered second first before

theorem eulerDerivative_scaledPolynomial (terms : List (ℕ × ℝ)) (frequency amplitude : ℝ) :
    eulerDerivative (fun radius => amplitude * eulerProfilePolynomial terms (frequency*radius)) =
      fun radius => amplitude * eulerProfilePolynomial (eulerProfilePolynomialStep terms) (frequency*radius) := by
  funext radius
  have derivative := ((eulerProfilePolynomial_hasDerivAt terms (frequency*radius)).comp radius
    ((hasDerivAt_id radius).const_mul frequency)).const_mul amplitude
  change radius * deriv (fun point => amplitude * eulerProfilePolynomial terms (frequency*point)) radius = _
  simp only [Function.comp_apply,mul_one] at derivative
  rw [derivative.deriv,eulerProfilePolynomial_step]
  ring

/-- Literal manuscript phase; the original sigma and negative gamma sign
are preserved before differentiating. -/
theorem radialPhase_profileRay (parameters : PhaseParameters) (cell : ℤ) :
    (fun radius => radialPhase parameters radius cell) =
      fun radius => parameters.sigma0*cellFrequency cell -
        parameters.gamma*eulerProfileRay (cellFrequency cell*radius) := by
  funext radius
  simp only [radialPhase,eulerProfileRay,profile,phaseRadialRay_apply_norm,sq_abs,mul_pow]

theorem radialPhase_euler_first (parameters : PhaseParameters) (cell : ℤ) :
    eulerDerivative (fun radius => radialPhase parameters radius cell) =
      fun radius => -parameters.gamma * positiveEulerProfile 0 (cellFrequency cell*radius) := by
  rw [radialPhase_profileRay]
  funext radius
  have derivative := ((((eulerProfileRay_smooth.differentiable (by simp)
    (cellFrequency cell*radius)).hasDerivAt).comp radius
    ((hasDerivAt_id radius).const_mul (cellFrequency cell))).const_mul parameters.gamma).const_sub
      (parameters.sigma0*cellFrequency cell)
  change radius * deriv (fun point => parameters.sigma0*cellFrequency cell -
    parameters.gamma*eulerProfileRay (cellFrequency cell*point)) radius = _
  simp only [Function.comp_apply,mul_one] at derivative
  rw [derivative.deriv]
  change radius * (-(parameters.gamma * (deriv eulerProfileRay (cellFrequency cell*radius) * cellFrequency cell))) =
    -parameters.gamma * (1 * ((cellFrequency cell*radius)^1 * iteratedDeriv 1 eulerProfileRay (cellFrequency cell*radius)) + 0)
  simp only [one_mul,add_zero,pow_one,iteratedDeriv_one]
  ring

/-- Every positive actual Euler phase derivative is the finite original
profile expansion at r lambda, with its literal negative gamma sign. -/
theorem radialPhase_positiveEuler (parameters : PhaseParameters) (cell : ℤ) (order : ℕ) :
    eulerIteratedDerivative (order+1) (fun radius => radialPhase parameters radius cell) =
      fun radius => -parameters.gamma * positiveEulerProfile order (cellFrequency cell*radius) := by
  induction order with
  | zero => exact radialPhase_euler_first parameters cell
  | succ order previous =>
      change eulerDerivative (eulerIteratedDerivative (order+1)
        (fun radius => radialPhase parameters radius cell)) = _
      rw [previous]
      exact eulerDerivative_scaledPolynomial (positiveEulerTerms order) (cellFrequency cell) (-parameters.gamma)

def positiveEulerPhaseConstant (parameters : PhaseParameters) (order : ℕ) : ℝ :=
  parameters.gamma * (eulerProfileValueConstant (positiveEulerTerms order) +
    eulerProfileDerivativeConstant (positiveEulerTerms order))

theorem positiveEulerPhaseConstant_nonnegative (parameters : PhaseParameters) (order : ℕ) :
    0 ≤ positiveEulerPhaseConstant parameters order :=
  mul_nonneg parameters.gamma_pos.le (add_nonneg (eulerProfileValueConstant_nonnegative _)
    (eulerProfileDerivativeConstant_nonnegative _))

/-- SR11's first bound at the original phase, uniformly down to the axis. -/
theorem radialPhase_positiveEuler_bound (parameters : PhaseParameters) (order : ℕ)
    (cell : ℤ) (radius : ℝ) (inside : radius ∈ Icc 0 1) :
    ‖eulerIteratedDerivative (order+1) (fun point => radialPhase parameters point cell) radius‖ ≤
      positiveEulerPhaseConstant parameters order * cellFrequency cell := by
  have frequency0 := (cellFrequency_pos cell).le
  have value0 := eulerProfileValueConstant_nonnegative (positiveEulerTerms order)
  have derivative0 := eulerProfileDerivativeConstant_nonnegative (positiveEulerTerms order)
  rw [radialPhase_positiveEuler,norm_mul,norm_neg,Real.norm_of_nonneg parameters.gamma_pos.le]
  calc
    _ ≤ parameters.gamma * (eulerProfileValueConstant (positiveEulerTerms order) *
        (cellFrequency cell*radius)) := by
      apply mul_le_mul_of_nonneg_left _ parameters.gamma_pos.le
      simpa only [positiveEulerProfile,abs_of_nonneg (mul_nonneg frequency0 inside.1)] using
        eulerProfilePolynomial_bound (positiveEulerTerms order) (cellFrequency cell*radius)
    _ = (parameters.gamma * eulerProfileValueConstant (positiveEulerTerms order) * cellFrequency cell) * radius := by ring
    _ ≤ parameters.gamma * eulerProfileValueConstant (positiveEulerTerms order) * cellFrequency cell :=
      mul_le_of_le_one_right (mul_nonneg (mul_nonneg parameters.gamma_pos.le value0) frequency0) inside.2
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right derivative0) parameters.gamma_pos.le) frequency0

/-- SR11's sharp phase commutator: positive Euler order is paid solely by
displacement, with no additional input-cell derivative or width reduction. -/
theorem radialPhase_positiveEuler_difference (parameters : PhaseParameters) (order : ℕ)
    (output input : ℤ) (radius : ℝ) (nonnegative : 0 ≤ radius) :
    ‖eulerIteratedDerivative (order+1) (fun point => radialPhase parameters point output) radius -
      eulerIteratedDerivative (order+1) (fun point => radialPhase parameters point input) radius‖ ≤
      positiveEulerPhaseConstant parameters order * radius * |((output-input : ℤ) : ℝ)| := by
  have value0 := eulerProfileValueConstant_nonnegative (positiveEulerTerms order)
  have derivative0 := eulerProfileDerivativeConstant_nonnegative (positiveEulerTerms order)
  have cells : |cellFrequency output-cellFrequency input| ≤ |((output-input : ℤ) : ℝ)| :=
    cell_lipschitz output input
  rw [radialPhase_positiveEuler,radialPhase_positiveEuler,← mul_sub,norm_mul,norm_neg,
    Real.norm_of_nonneg parameters.gamma_pos.le]
  calc
    _ ≤ parameters.gamma * (eulerProfileDerivativeConstant (positiveEulerTerms order) *
        |cellFrequency output*radius-cellFrequency input*radius|) :=
      mul_le_mul_of_nonneg_left (eulerProfilePolynomial_difference (positiveEulerTerms order)
        (cellFrequency input*radius) (cellFrequency output*radius)) parameters.gamma_pos.le
    _ = parameters.gamma * eulerProfileDerivativeConstant (positiveEulerTerms order) * radius *
        |cellFrequency output-cellFrequency input| := by
      rw [← sub_mul,abs_mul,abs_of_nonneg nonnegative]
      ring
    _ ≤ parameters.gamma * eulerProfileDerivativeConstant (positiveEulerTerms order) * radius *
        |((output-input : ℤ) : ℝ)| :=
      mul_le_mul_of_nonneg_left cells (mul_nonneg (mul_nonneg parameters.gamma_pos.le derivative0) nonnegative)
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left value0) parameters.gamma_pos.le) nonnegative) (abs_nonneg _)

end Grad.OriginalCartesianTameEstimate
