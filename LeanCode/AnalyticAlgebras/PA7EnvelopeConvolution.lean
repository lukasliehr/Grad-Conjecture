import PA6Translation

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.PhaseAlgebra

open Grad.CartesianState

universe valueUniverse

variable {Value : Type valueUniverse} [NormedAddCommGroup Value]

/-- Each square-summable component is bounded by the full norm. -/
theorem component_norm_le (field : lp (fun _ : ℤ => Value) 2) (cell : ℤ) :
    ‖field cell‖ ≤ ‖field‖ := by
  have normFormula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at normFormula
  have summableSq : Summable (fun inner : ℤ => ‖field inner‖ ^ 2) :=
    (memlp_iff_summable_sq _).mp (lp.memℓp field)
  have squares : ‖field cell‖ ^ 2 ≤ ‖field‖ ^ 2 := by
    rw [normFormula]
    exact summableSq.le_tsum cell (fun inner _ => sq_nonneg _)
  calc ‖field cell‖
      = Real.sqrt (‖field cell‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖field‖ ^ 2) := Real.sqrt_le_sqrt squares
    _ = ‖field‖ := Real.sqrt_sq (norm_nonneg _)

variable [NormedSpace ℝ Value]

/-- The bounded evaluation of a square-summable sequence at one cell. -/
def evaluationMap (cell : ℤ) : lp (fun _ : ℤ => Value) 2 →L[ℝ] Value :=
  LinearMap.mkContinuous
    { toFun := fun field => field cell
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun field => by rw [one_mul]; exact component_norm_le field cell)

theorem evaluationMap_apply (cell : ℤ) (field : lp (fun _ : ℤ => Value) 2) :
    evaluationMap cell field = field cell := rfl

theorem envelope_translate_norm (envelope : ℤ → ℝ)
    (nonneg : ∀ cell, 0 ≤ envelope cell) (shift : ℤ)
    (field : lp (fun _ : ℤ => Value) 2) :
    ‖envelope shift • translateSequence shift field‖ = envelope shift * ‖field‖ := by
  rw [norm_smul, translateSequence_norm, Real.norm_eq_abs,
    abs_of_nonneg (nonneg shift)]

theorem envelope_translate_norm_summable (envelope : ℤ → ℝ)
    (nonneg : ∀ cell, 0 ≤ envelope cell) (summable : Summable envelope)
    (field : lp (fun _ : ℤ => Value) 2) :
    Summable (fun shift : ℤ =>
      ‖envelope shift • translateSequence shift field‖) :=
  (summable.mul_right ‖field‖).congr
    (fun shift => (envelope_translate_norm envelope nonneg shift field).symm)

variable [CompleteSpace Value]

theorem envelope_translate_summable (envelope : ℤ → ℝ)
    (nonneg : ∀ cell, 0 ≤ envelope cell) (summable : Summable envelope)
    (field : lp (fun _ : ℤ => Value) 2) :
    Summable (fun shift : ℤ => envelope shift • translateSequence shift field) :=
  Summable.of_norm (envelope_translate_norm_summable envelope nonneg summable field)

/-- Convolution by a nonnegative summable envelope, as the absolutely
convergent series of weighted translations. -/
def envelopeConvolution (envelope : ℤ → ℝ)
    (nonneg : ∀ cell, 0 ≤ envelope cell) (summable : Summable envelope) :
    lp (fun _ : ℤ => Value) 2 →L[ℝ] lp (fun _ : ℤ => Value) 2 :=
  LinearMap.mkContinuous
    { toFun := fun field => ∑' shift, envelope shift • translateSequence shift field
      map_add' := fun first second => by
        have split : (fun shift : ℤ =>
            envelope shift • translateSequence shift (first + second)) =
            fun shift : ℤ => envelope shift • translateSequence shift first +
              envelope shift • translateSequence shift second := by
          funext shift
          rw [translateSequence_add, smul_add]
        rw [split, Summable.tsum_add
          (envelope_translate_summable envelope nonneg summable first)
          (envelope_translate_summable envelope nonneg summable second)]
      map_smul' := fun scalar field => by
        have split : (fun shift : ℤ =>
            envelope shift • translateSequence shift (scalar • field)) =
            fun shift : ℤ =>
              scalar • (envelope shift • translateSequence shift field) := by
          funext shift
          rw [translateSequence_smul, smul_comm]
        rw [RingHom.id_apply, split]
        exact ((envelope_translate_summable envelope nonneg summable
          field).hasSum.mapL (scalar • ContinuousLinearMap.id ℝ
            (lp (fun _ : ℤ => Value) 2))).tsum_eq }
    (∑' cell, envelope cell)
    (fun field => by
      calc ‖∑' shift, envelope shift • translateSequence shift field‖
          ≤ ∑' shift, ‖envelope shift • translateSequence shift field‖ :=
            norm_tsum_le_tsum_norm
              (envelope_translate_norm_summable envelope nonneg summable field)
        _ = ∑' shift, envelope shift * ‖field‖ := by
            congr 1
            funext shift
            rw [envelope_translate_norm envelope nonneg shift field]
        _ = (∑' cell, envelope cell) * ‖field‖ := tsum_mul_right)

/-- The norm bound is exactly the envelope l1 mass. -/
theorem envelopeConvolution_norm_le (envelope : ℤ → ℝ)
    (nonneg : ∀ cell, 0 ≤ envelope cell) (summable : Summable envelope) :
    ‖envelopeConvolution (Value := Value) envelope nonneg summable‖ ≤
      ∑' cell, envelope cell :=
  LinearMap.mkContinuous_norm_le _ (tsum_nonneg nonneg) _

/-- The literal convolution coefficient law. -/
theorem envelopeConvolution_apply (envelope : ℤ → ℝ)
    (nonneg : ∀ cell, 0 ≤ envelope cell) (summable : Summable envelope)
    (field : lp (fun _ : ℤ => Value) 2) (cell : ℤ) :
    envelopeConvolution envelope nonneg summable field cell =
      ∑' shift, envelope shift • field (cell - shift) := by
  have evaluated := ((envelope_translate_summable envelope nonneg summable
    field).hasSum.mapL (evaluationMap (Value := Value) cell)).tsum_eq
  calc envelopeConvolution envelope nonneg summable field cell
      = evaluationMap cell
          (∑' shift, envelope shift • translateSequence shift field) := rfl
    _ = ∑' shift, evaluationMap cell
          (envelope shift • translateSequence shift field) := evaluated.symm
    _ = ∑' shift, envelope shift • field (cell - shift) := rfl

end Grad.PhaseAlgebra
