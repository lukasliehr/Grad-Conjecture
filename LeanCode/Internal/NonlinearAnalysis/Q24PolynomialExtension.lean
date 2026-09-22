import Q24PolynomialCarrier
import BanachAdapterSlot

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.Q24Realization

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearQuotientBounds Grad.NonlinearProduct
open Grad.AxisCore Grad.QuotientProjection

section Slots

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A scalar source slot lets the accepted NG_F07 slot-completion theorem
cover ordinary multilinear maps, including the degree-zero term. -/
def scalarSourceLinear : E →ₗ[ℝ] ((⊤ : Submodule ℝ ℝ) →ₗ[ℝ] E) where
  toFun value := (⊤ : Submodule ℝ ℝ).subtype.smulRight value
  map_add' first second := by ext scalar; exact smul_add _ _ _
  map_smul' scalar value := by ext source; exact smul_comm _ _ _

theorem multilinearCompletion_exists (core : Submodule ℝ X) (dense : Dense (core : Set X))
    (arity : ℕ) (mapping : MultilinearMap ℝ (fun _ : Fin arity => core) E)
    (constant : ℝ) (nonneg : 0 ≤ constant)
    (bounded : ∀ arguments, ‖mapping arguments‖ ≤ constant * ∏ position, ‖arguments position‖) :
    ∃ completed : ContinuousMultilinearMap ℝ (fun _ : Fin arity => X) E,
      ∀ arguments : Fin arity → core,
        completed (fun position => (arguments position : X)) = mapping arguments := by
  let withSource := scalarSourceLinear.compMultilinearMap mapping
  have sourceDense : Dense ((⊤ : Submodule ℝ ℝ) : Set ℝ) := dense_univ
  obtain ⟨completed, agrees⟩ := Grad.FiniteBanachCalculus.slotCompletion_exists
    dense sourceDense arity withSource constant nonneg (by
      intro arguments source
      change ‖(source : ℝ) • mapping arguments‖ ≤ _
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_left (bounded arguments) (norm_nonneg (source : ℝ))).trans_eq
        (by change ‖(source : ℝ)‖ * (constant * ∏ position, ‖arguments position‖) =
          constant * (∏ position, ‖arguments position‖) * ‖(source : ℝ)‖; ring))
  refine ⟨(ContinuousLinearMap.apply ℝ E (1 : ℝ)).compContinuousMultilinearMap completed, ?_⟩
  intro arguments
  change completed (fun position => (arguments position : X)) (1 : ℝ) = _
  have equality := agrees arguments (⟨1, Submodule.mem_top⟩ : (⊤ : Submodule ℝ ℝ))
  change completed (fun position => (arguments position : X)) (1 : ℝ) = (1 : ℝ) • mapping arguments at equality
  simpa only [one_smul] using equality

end Slots

def homogeneousCoreMap (parameters : PhaseParameters) (grade arity : ℕ)
    (mapping : MultilinearMap ℂ (fun _ : Fin arity => QuotientState parameters)
      (QuotientRows parameters)) :
    MultilinearMap ℝ (fun _ : Fin arity => PolynomialCore parameters (grade + 6))
      (ZAmbient parameters grade) :=
  ((quotientEta parameters grade).restrictScalars ℝ).compMultilinearMap
    ((mapping.restrictScalars ℝ).compLinearMap
      (fun _ => (polynomialCoreEquiv parameters (grade + 6)).symm.toLinearMap))

theorem homogeneousCompletion_exists (parameters : PhaseParameters) (grade arity : ℕ)
    (mapping : MultilinearMap ℂ (fun _ : Fin arity => QuotientState parameters)
      (QuotientRows parameters))
    (bounded : ∃ constant : ℝ, 0 ≤ constant ∧ ∀ arguments,
      rowsGradeNorm grade (mapping arguments) ≤
        constant * ∏ position, stateNorm (grade + 6) (arguments position)) :
    ∃ completed : ContinuousMultilinearMap ℝ
        (fun _ : Fin arity => PolynomialState parameters (grade + 6)) (ZAmbient parameters grade),
      ∀ arguments : Fin arity → QuotientState parameters,
        completed (fun position => polynomialStateEmbed parameters (grade + 6) (arguments position)) =
          quotientEta parameters grade (mapping arguments) := by
  obtain ⟨constant, nonneg, bounded⟩ := bounded
  obtain ⟨completed, agrees⟩ := multilinearCompletion_exists
    (PolynomialCore parameters (grade + 6)) (polynomialCore_dense parameters (grade + 6))
    arity (homogeneousCoreMap parameters grade arity mapping) (2 * constant) (by positivity) (by
      intro arguments
      change ‖quotientEta parameters grade
        (mapping (fun position => (polynomialCoreEquiv parameters (grade + 6)).symm (arguments position)))‖ ≤ _
      apply (quotientEta_norm_le_rows parameters grade _).trans
      apply (mul_le_mul_of_nonneg_left (bounded _) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
      simp only [polynomialCoreEquiv_symm_norm]
      ring)
  refine ⟨completed, fun arguments => ?_⟩
  have equality := agrees (fun position => polynomialCoreEquiv parameters (grade + 6) (arguments position))
  change completed (fun position => polynomialStateEmbed parameters (grade + 6) (arguments position)) =
    quotientEta parameters grade (mapping (fun position =>
      (polynomialCoreEquiv parameters (grade + 6)).symm
        (polynomialCoreEquiv parameters (grade + 6) (arguments position)))) at equality
  simpa only [LinearEquiv.symm_apply_apply] using equality

theorem homogeneousCompletion_of_oneHigh (parameters : PhaseParameters) (grade arity : ℕ)
    (mapping : MultilinearMap ℂ (fun _ : Fin arity => QuotientState parameters)
      (QuotientRows parameters))
    (bounded : ∃ constant : ℝ, 0 ≤ constant ∧ ∀ arguments,
      rowsGradeNorm grade (mapping arguments) ≤ constant * oneHighArgumentSum grade arguments) :
    ∃ completed : ContinuousMultilinearMap ℝ
        (fun _ : Fin arity => PolynomialState parameters (grade + 6)) (ZAmbient parameters grade),
      ∀ arguments : Fin arity → QuotientState parameters,
        completed (fun position => polynomialStateEmbed parameters (grade + 6) (arguments position)) =
          quotientEta parameters grade (mapping arguments) := by
  apply homogeneousCompletion_exists
  obtain ⟨constant, nonneg, bounded⟩ := bounded
  refine ⟨constant * arity, by positivity, fun arguments => ?_⟩
  exact (bounded arguments).trans ((mul_le_mul_of_nonneg_left
    (oneHighArgumentSum_le_product parameters grade arity arguments) nonneg).trans_eq (by ring))

end Grad.Q24Realization
