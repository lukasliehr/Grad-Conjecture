import Q24SeedTransfer
import QP5Norms

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.Q24Realization

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearQuotientBounds Grad.NonlinearProduct
open Grad.Constraints Grad.SmoothingFamily Grad.AxisCore Grad.ImplementationReadiness

/-- Intermediate Q4 state, with its literal scalar/vector/potential sum norm. -/
abbrev PolynomialState (parameters : PhaseParameters) (grade : ℕ) :=
  StateAmbient ℂ (AGrade parameters 3 grade) (AGrade parameters 1 grade)

def polynomialStateEmbed (parameters : PhaseParameters) (grade : ℕ) :
    QuotientState parameters →ₗ[ℂ] PolynomialState parameters grade where
  toFun state := statePack state.1 (fieldEmbed parameters 3 grade state.2.1)
    (fieldEmbed parameters 1 grade state.2.2)
  map_add' first second := by
    apply (WithLp.equiv 1 _).injective
    apply Prod.ext
    · rfl
    · apply (WithLp.equiv 1 _).injective
      exact Prod.ext (map_add _ _ _) (map_add _ _ _)
  map_smul' scalar state := by
    apply (WithLp.equiv 1 _).injective
    apply Prod.ext
    · rfl
    · apply (WithLp.equiv 1 _).injective
      exact Prod.ext (map_smul _ _ _) (map_smul _ _ _)

theorem polynomialStateEmbed_norm (parameters : PhaseParameters) (grade : ℕ)
    (state : QuotientState parameters) :
    ‖polynomialStateEmbed parameters grade state‖ = stateNorm grade state := by
  change ‖statePack _ _ _‖ = _
  rw [statePack_norm, fieldEmbed_norm, fieldEmbed_norm]
  rfl

theorem fieldEmbed_injective (parameters : PhaseParameters) (dimension grade : ℕ) :
    Function.Injective (fieldEmbed parameters dimension grade) := by
  intro first second equality
  exact congrArg GradeCore.toCore (aGradeEta_injective parameters equality)

theorem fieldEmbed_denseRange (parameters : PhaseParameters) (dimension grade : ℕ) :
    DenseRange (fieldEmbed parameters dimension grade) := by
  apply (aGradeEta_denseRange parameters).mono
  rintro _ ⟨field, rfl⟩
  exact ⟨field.toCore, by simp only [fieldEmbed, LinearMap.comp_apply,
    GradeCore.ofCore_toCore, LinearIsometry.coe_toLinearMap]⟩

theorem polynomialStateEmbed_injective (parameters : PhaseParameters) (grade : ℕ) :
    Function.Injective (polynomialStateEmbed parameters grade) := by
  intro first second equality
  have scalar := congrArg (fun value : PolynomialState parameters grade => value.ofLp.1) equality
  have vector := congrArg (fun value : PolynomialState parameters grade => value.ofLp.2.ofLp.1) equality
  have potential := congrArg (fun value : PolynomialState parameters grade => value.ofLp.2.ofLp.2) equality
  exact Prod.ext scalar (Prod.ext (fieldEmbed_injective parameters 3 grade vector)
    (fieldEmbed_injective parameters 1 grade potential))

theorem polynomialStateEmbed_denseRange (parameters : PhaseParameters) (grade : ℕ) :
    DenseRange (polynomialStateEmbed parameters grade) := by
  let inner := (WithLp.prodContinuousLinearEquiv 1 ℝ
    (AGrade parameters 3 grade) (AGrade parameters 1 grade)).symm
  let outer := (WithLp.prodContinuousLinearEquiv 1 ℝ ℂ
    (WithLp 1 (AGrade parameters 3 grade × AGrade parameters 1 grade))).symm
  have innerDense := inner.surjective.denseRange.comp
    ((fieldEmbed_denseRange parameters 3 grade).prodMap
      (fieldEmbed_denseRange parameters 1 grade)) inner.continuous
  exact outer.surjective.denseRange.comp
    (denseRange_id.prodMap innerDense) outer.continuous

abbrev PolynomialCore (parameters : PhaseParameters) (grade : ℕ) :
    Submodule ℝ (PolynomialState parameters grade) :=
  ((polynomialStateEmbed parameters grade).restrictScalars ℝ).range

def polynomialCoreEquiv (parameters : PhaseParameters) (grade : ℕ) :
    QuotientState parameters ≃ₗ[ℝ] PolynomialCore parameters grade :=
  LinearEquiv.ofInjective ((polynomialStateEmbed parameters grade).restrictScalars ℝ)
    (polynomialStateEmbed_injective parameters grade)

theorem polynomialCore_dense (parameters : PhaseParameters) (grade : ℕ) :
    Dense (PolynomialCore parameters grade : Set (PolynomialState parameters grade)) :=
  polynomialStateEmbed_denseRange parameters grade

theorem polynomialCoreEquiv_norm (parameters : PhaseParameters) (grade : ℕ)
    (state : QuotientState parameters) :
    ‖polynomialCoreEquiv parameters grade state‖ = stateNorm grade state :=
  polynomialStateEmbed_norm parameters grade state

theorem polynomialCoreEquiv_symm_norm (parameters : PhaseParameters) (grade : ℕ)
    (state : PolynomialCore parameters grade) :
    stateNorm grade ((polynomialCoreEquiv parameters grade).symm state) = ‖state‖ := by
  rw [← polynomialCoreEquiv_norm, LinearEquiv.apply_symm_apply]

/-- Estimate only: the target remains the original fourfold Hilbert space,
not the auxiliary row-sum seminorm used in the Q4 core estimate. -/
theorem quotientEta_norm_le_rows (parameters : PhaseParameters) (grade : ℕ)
    (rows : QuotientRows parameters) :
    ‖Grad.QuotientProjection.quotientEta parameters grade rows‖ ≤ 2 * rowsGradeNorm grade rows := by
  apply Grad.QuotientProjection.quotientNorm_le_two_mul
  · exact Finset.sum_nonneg fun _ _ => originalGradeNorm_nonnegative _ _
  · intro coordinate
    exact Finset.single_le_sum (fun _ _ => originalGradeNorm_nonnegative _ _)
      (Finset.mem_univ coordinate)

theorem oneHighArgumentSum_le_product (parameters : PhaseParameters) (grade arity : ℕ)
    (arguments : Fin arity → QuotientState parameters) :
    oneHighArgumentSum grade arguments ≤
      arity * ∏ position, stateNorm (grade + 6) (arguments position) := by
  unfold oneHighArgumentSum
  calc
    (∑ position, stateNorm (grade + 6) (arguments position) *
        ∏ other ∈ Finset.univ.erase position, stateNorm 4 (arguments other)) ≤
      ∑ position : Fin arity, ∏ other, stateNorm (grade + 6) (arguments other) := by
        apply Finset.sum_le_sum
        intro position _
        calc
          _ ≤ stateNorm (grade + 6) (arguments position) *
              ∏ other ∈ Finset.univ.erase position, stateNorm (grade + 6) (arguments other) :=
            mul_le_mul_of_nonneg_left
              (Finset.prod_le_prod (fun _ _ => stateNorm_nonneg _ _)
                (fun _ _ => stateNorm_mono (by omega) _)) (stateNorm_nonneg _ _)
          _ = _ := Finset.mul_prod_erase Finset.univ
            (fun other => stateNorm (grade + 6) (arguments other)) (Finset.mem_univ position)
    _ = _ := by simp

end Grad.Q24Realization
