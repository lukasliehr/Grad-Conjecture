import TameRootSeries

noncomputable section

set_option maxHeartbeats 1600000

open Filter
open scoped BigOperators Topology

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! Genuine directional differentiability of coefficient-core valued curves,
measured simultaneously in every graded envelope: the difference-quotient
predicate and its constant, linear, sum, scalar, product and finite-product
calculus.  This is the coefficient-level engine behind the Q15/Q20 chart
derivative tower. -/

variable {parameters : PhaseParameters}

theorem coefficientEnvelope_zero (grade : ℕ) :
    coefficientEnvelope grade (0 : TameCoefficient parameters) = 0 := by
  rw [coefficientEnvelope, tameZero_val, tameEnvelope]
  have vanish : (fun cell => tameEnvelopeTerm parameters grade (0 : ℤ → ℂ) cell) =
      fun _ => (0 : ℝ) := by
    funext cell
    rw [tameEnvelopeTerm, Pi.zero_apply, norm_zero, mul_zero]
  rw [vanish]
  exact tsum_zero

/-- Genuine derivative of a coefficient-core curve at zero, in every graded
envelope at once. -/
def HasEnvDerivAt (curve : ℝ → TameCoefficient parameters)
    (derivative : TameCoefficient parameters) : Prop :=
  ∀ grade : ℕ, Tendsto (fun t : ℝ => coefficientEnvelope grade
      ((((t : ℂ))⁻¹ • (curve t - curve 0)) - derivative))
    (𝓝[≠] (0 : ℝ)) (𝓝 0)

theorem HasEnvDerivAt.congr_curve {firstCurve secondCurve : ℝ → TameCoefficient parameters}
    {derivative : TameCoefficient parameters} (differentiable : HasEnvDerivAt firstCurve derivative)
    (agree : ∀ t, secondCurve t = firstCurve t) : HasEnvDerivAt secondCurve derivative := by
  intro grade
  have rewrite : (fun t : ℝ => coefficientEnvelope grade
      ((((t : ℂ))⁻¹ • (secondCurve t - secondCurve 0)) - derivative)) =
      fun t : ℝ => coefficientEnvelope grade
        ((((t : ℂ))⁻¹ • (firstCurve t - firstCurve 0)) - derivative) := by
    funext t
    rw [agree t, agree 0]
  rw [rewrite]
  exact differentiable grade

theorem hasEnvDerivAt_const (value : TameCoefficient parameters) :
    HasEnvDerivAt (fun _ => value) 0 := by
  intro grade
  have vanish : (fun t : ℝ => coefficientEnvelope grade
      ((((t : ℂ))⁻¹ • ((fun _ : ℝ => value) t - (fun _ : ℝ => value) 0)) - 0)) =
      fun _ => (0 : ℝ) := by
    funext t
    have zero_argument : (((t : ℂ))⁻¹ • (value - value)) - 0 =
        (0 : TameCoefficient parameters) := by
      rw [sub_self, smul_zero, sub_zero]
    rw [zero_argument, coefficientEnvelope_zero]
  rw [vanish]
  exact tendsto_const_nhds

/-- An affine curve has its slope as genuine derivative. -/
theorem hasEnvDerivAt_affine (base slope : TameCoefficient parameters) :
    HasEnvDerivAt (fun t : ℝ => base + (t : ℂ) • slope) slope := by
  intro grade
  apply squeeze_zero' (Eventually.of_forall (fun _ => coefficientEnvelope_nonneg _ _))
    (g := fun _ => (0 : ℝ)) ?_ tendsto_const_nhds
  apply eventually_nhdsWithin_of_forall
  intro t membership
  have nonzero : (t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by simpa using membership)
  have collapse : (((t : ℂ))⁻¹ • ((base + (t : ℂ) • slope) - (base + ((0 : ℝ) : ℂ) • slope)))
      - slope = (0 : TameCoefficient parameters) := by
    rw [Complex.ofReal_zero, zero_smul, add_zero, add_sub_cancel_left, smul_smul,
      inv_mul_cancel₀ nonzero, one_smul, sub_self]
  rw [collapse, coefficientEnvelope_zero]

theorem HasEnvDerivAt.add {firstCurve secondCurve : ℝ → TameCoefficient parameters}
    {firstDerivative secondDerivative : TameCoefficient parameters}
    (first : HasEnvDerivAt firstCurve firstDerivative)
    (second : HasEnvDerivAt secondCurve secondDerivative) :
    HasEnvDerivAt (fun t => firstCurve t + secondCurve t)
      (firstDerivative + secondDerivative) := by
  intro grade
  apply squeeze_zero' (Eventually.of_forall (fun _ => coefficientEnvelope_nonneg _ _))
    (g := fun t : ℝ => coefficientEnvelope grade
        ((((t : ℂ))⁻¹ • (firstCurve t - firstCurve 0)) - firstDerivative) +
      coefficientEnvelope grade
        ((((t : ℂ))⁻¹ • (secondCurve t - secondCurve 0)) - secondDerivative)) ?_ ?_
  · apply Eventually.of_forall
    intro t
    have split : (((t : ℂ))⁻¹ • ((firstCurve t + secondCurve t) -
        (firstCurve 0 + secondCurve 0))) - (firstDerivative + secondDerivative) =
        ((((t : ℂ))⁻¹ • (firstCurve t - firstCurve 0)) - firstDerivative) +
          ((((t : ℂ))⁻¹ • (secondCurve t - secondCurve 0)) - secondDerivative) := by
      rw [add_sub_add_comm, smul_add]
      abel
    rw [split]
    exact coefficientEnvelope_add_le grade _ _
  · have limit := (first grade).add (second grade)
    rw [add_zero] at limit
    exact limit

theorem HasEnvDerivAt.const_smul {curve : ℝ → TameCoefficient parameters}
    {derivative : TameCoefficient parameters} (scalar : ℂ)
    (differentiable : HasEnvDerivAt curve derivative) :
    HasEnvDerivAt (fun t => scalar • curve t) (scalar • derivative) := by
  intro grade
  have rewrite : (fun t : ℝ => coefficientEnvelope grade
      ((((t : ℂ))⁻¹ • (scalar • curve t - scalar • curve 0)) - scalar • derivative)) =
      fun t : ℝ => ‖scalar‖ * coefficientEnvelope grade
        ((((t : ℂ))⁻¹ • (curve t - curve 0)) - derivative) := by
    funext t
    have pull : (((t : ℂ))⁻¹ • (scalar • curve t - scalar • curve 0)) - scalar • derivative =
        scalar • ((((t : ℂ))⁻¹ • (curve t - curve 0)) - derivative) := by
      rw [← smul_sub scalar (curve t) (curve 0), smul_comm (((t : ℂ))⁻¹) scalar,
        ← smul_sub scalar ((((t : ℂ))⁻¹ • (curve t - curve 0))) derivative]
    rw [pull, coefficientEnvelope_smul]
  rw [rewrite]
  have limit := (differentiable grade).const_mul ‖scalar‖
  rw [mul_zero] at limit
  exact limit

/-- Local linear growth: a differentiable curve moves at most linearly near
zero, in every grade. -/
theorem HasEnvDerivAt.difference_le {curve : ℝ → TameCoefficient parameters}
    {derivative : TameCoefficient parameters}
    (differentiable : HasEnvDerivAt curve derivative) (grade : ℕ) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), coefficientEnvelope grade (curve t - curve 0) ≤
      |t| * (coefficientEnvelope grade derivative + 1) := by
  have eventually_small := (differentiable grade).eventually_le_const zero_lt_one
  apply eventually_small.mp
  apply eventually_nhdsWithin_of_forall
  intro t membership quotient_small
  have nonzero : (t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by simpa using membership)
  have reconstruct : curve t - curve 0 =
      (t : ℂ) • (((((t : ℂ))⁻¹ • (curve t - curve 0)) - derivative) + derivative) := by
    rw [sub_add_cancel, smul_smul, mul_inv_cancel₀ nonzero, one_smul]
  have envelope_eq : coefficientEnvelope grade (curve t - curve 0) =
      ‖(t : ℂ)‖ * coefficientEnvelope grade
        (((((t : ℂ))⁻¹ • (curve t - curve 0)) - derivative) + derivative) := by
    rw [← coefficientEnvelope_smul]
    exact congrArg (coefficientEnvelope grade) reconstruct
  calc coefficientEnvelope grade (curve t - curve 0)
      = ‖(t : ℂ)‖ * coefficientEnvelope grade
          (((((t : ℂ))⁻¹ • (curve t - curve 0)) - derivative) + derivative) := envelope_eq
    _ ≤ ‖(t : ℂ)‖ * (coefficientEnvelope grade
          ((((t : ℂ))⁻¹ • (curve t - curve 0)) - derivative) +
          coefficientEnvelope grade derivative) :=
        mul_le_mul_of_nonneg_left (coefficientEnvelope_add_le grade _ _) (norm_nonneg _)
    _ ≤ |t| * (coefficientEnvelope grade derivative + 1) := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg t)
        linarith

theorem HasEnvDerivAt.tendsto_difference {curve : ℝ → TameCoefficient parameters}
    {derivative : TameCoefficient parameters}
    (differentiable : HasEnvDerivAt curve derivative) (grade : ℕ) :
    Tendsto (fun t : ℝ => coefficientEnvelope grade (curve t - curve 0))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => coefficientEnvelope_nonneg _ _))
    (differentiable.difference_le grade)
  have limit : Tendsto (fun t : ℝ => |t| * (coefficientEnvelope grade derivative + 1))
      (𝓝 (0 : ℝ)) (𝓝 0) := by
    have shape : Tendsto (fun t : ℝ => |t| * (coefficientEnvelope grade derivative + 1))
        (𝓝 (0 : ℝ)) (𝓝 (|(0 : ℝ)| * (coefficientEnvelope grade derivative + 1))) :=
      (continuous_abs.mul continuous_const).tendsto 0
    simpa using shape
  exact limit.mono_left nhdsWithin_le_nhds

theorem HasEnvDerivAt.tendsto_envelope {curve : ℝ → TameCoefficient parameters}
    {derivative : TameCoefficient parameters}
    (differentiable : HasEnvDerivAt curve derivative) (grade : ℕ) :
    Tendsto (fun t : ℝ => coefficientEnvelope grade (curve t))
      (𝓝[≠] (0 : ℝ)) (𝓝 (coefficientEnvelope grade (curve 0))) := by
  have envelope_split (t : ℝ) : coefficientEnvelope grade (curve t) ≤
      coefficientEnvelope grade (curve t - curve 0) +
        coefficientEnvelope grade (curve 0) := by
    calc coefficientEnvelope grade (curve t)
        = coefficientEnvelope grade ((curve t - curve 0) + curve 0) := by
          rw [sub_add_cancel]
      _ ≤ _ := coefficientEnvelope_add_le grade _ _
  have envelope_reverse (t : ℝ) : coefficientEnvelope grade (curve 0) -
      coefficientEnvelope grade (curve t - curve 0) ≤
      coefficientEnvelope grade (curve t) := by
    have base_split : coefficientEnvelope grade (curve 0) ≤
        coefficientEnvelope grade (curve t - curve 0) +
          coefficientEnvelope grade (curve t) := by
      calc coefficientEnvelope grade (curve 0)
          = coefficientEnvelope grade ((curve 0 - curve t) + curve t) := by
            rw [sub_add_cancel]
        _ ≤ coefficientEnvelope grade (curve 0 - curve t) +
            coefficientEnvelope grade (curve t) := coefficientEnvelope_add_le grade _ _
        _ = _ := by
            rw [← coefficientEnvelope_neg grade (curve 0 - curve t), neg_sub]
    linarith
  have difference_limit := differentiable.tendsto_difference grade
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun t => coefficientEnvelope grade (curve 0) -
      coefficientEnvelope grade (curve t - curve 0))
    (h := fun t => coefficientEnvelope grade (curve t - curve 0) +
      coefficientEnvelope grade (curve 0))
    ?_ ?_ envelope_reverse envelope_split
  · have shape := (tendsto_const_nhds (α := ℝ)
      (x := coefficientEnvelope grade (curve 0))
      (f := 𝓝[≠] (0 : ℝ))).sub difference_limit
    simpa using shape
  · have shape := difference_limit.add (tendsto_const_nhds (α := ℝ)
      (x := coefficientEnvelope grade (curve 0)) (f := 𝓝[≠] (0 : ℝ)))
    simpa using shape

/-- The product rule for coefficient-core curves in every graded envelope. -/
theorem HasEnvDerivAt.mul {firstCurve secondCurve : ℝ → TameCoefficient parameters}
    {firstDerivative secondDerivative : TameCoefficient parameters}
    (first : HasEnvDerivAt firstCurve firstDerivative)
    (second : HasEnvDerivAt secondCurve secondDerivative) :
    HasEnvDerivAt (fun t => firstCurve t * secondCurve t)
      (firstDerivative * secondCurve 0 + firstCurve 0 * secondDerivative) := by
  intro grade
  set quotientOne := fun t : ℝ =>
    (((t : ℂ))⁻¹ • (firstCurve t - firstCurve 0)) - firstDerivative with quotientOne_def
  set quotientTwo := fun t : ℝ =>
    (((t : ℂ))⁻¹ • (secondCurve t - secondCurve 0)) - secondDerivative with quotientTwo_def
  have decompose (t : ℝ) (nonzero : (t : ℂ) ≠ 0) :
      (((t : ℂ))⁻¹ • (firstCurve t * secondCurve t - firstCurve 0 * secondCurve 0)) -
        (firstDerivative * secondCurve 0 + firstCurve 0 * secondDerivative) =
      (quotientOne t * secondCurve t) +
        (firstDerivative * (secondCurve t - secondCurve 0)) +
        (firstCurve 0 * quotientTwo t) := by
    rw [quotientOne_def, quotientTwo_def]
    have expand : firstCurve t * secondCurve t - firstCurve 0 * secondCurve 0 =
        (firstCurve t - firstCurve 0) * secondCurve t +
          firstCurve 0 * (secondCurve t - secondCurve 0) := by
      ring
    rw [expand, smul_add, ← tameSmul_mul, ← tameMul_smul]
    ring
  have majorized : ∀ᶠ (t : ℝ) in 𝓝[≠] (0 : ℝ), coefficientEnvelope grade
      ((((t : ℂ))⁻¹ • (firstCurve t * secondCurve t - firstCurve 0 * secondCurve 0)) -
        (firstDerivative * secondCurve 0 + firstCurve 0 * secondDerivative)) ≤
      (2 : ℝ) ^ grade *
          (coefficientEnvelope grade (quotientOne t) * coefficientEnvelope 0 (secondCurve t) +
            coefficientEnvelope 0 (quotientOne t) * coefficientEnvelope grade (secondCurve t)) +
        (2 : ℝ) ^ grade *
          (coefficientEnvelope grade firstDerivative *
              coefficientEnvelope 0 (secondCurve t - secondCurve 0) +
            coefficientEnvelope 0 firstDerivative *
              coefficientEnvelope grade (secondCurve t - secondCurve 0)) +
        (2 : ℝ) ^ grade *
          (coefficientEnvelope grade (firstCurve 0) * coefficientEnvelope 0 (quotientTwo t) +
            coefficientEnvelope 0 (firstCurve 0) * coefficientEnvelope grade (quotientTwo t)) := by
    apply eventually_nhdsWithin_of_forall
    intro t membership
    have nonzero : (t : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (by simpa using membership)
    rw [decompose t nonzero]
    calc coefficientEnvelope grade
          ((quotientOne t * secondCurve t) +
            (firstDerivative * (secondCurve t - secondCurve 0)) +
            (firstCurve 0 * quotientTwo t))
        ≤ coefficientEnvelope grade (quotientOne t * secondCurve t) +
            coefficientEnvelope grade (firstDerivative * (secondCurve t - secondCurve 0)) +
            coefficientEnvelope grade (firstCurve 0 * quotientTwo t) :=
          ((coefficientEnvelope_add_le grade _ _).trans
            (add_le_add (coefficientEnvelope_add_le grade _ _) le_rfl))
      _ ≤ _ :=
          add_le_add (add_le_add (tameMul_envelope_le grade _ _)
            (tameMul_envelope_le grade _ _)) (tameMul_envelope_le grade _ _)
  have termOne : Tendsto (fun t : ℝ => (2 : ℝ) ^ grade *
      (coefficientEnvelope grade (quotientOne t) * coefficientEnvelope 0 (secondCurve t) +
        coefficientEnvelope 0 (quotientOne t) * coefficientEnvelope grade (secondCurve t)))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have shape := (((first grade).mul (second.tendsto_envelope 0)).add
      ((first 0).mul (second.tendsto_envelope grade))).const_mul ((2 : ℝ) ^ grade)
    simpa using shape
  have termTwo : Tendsto (fun t : ℝ => (2 : ℝ) ^ grade *
      (coefficientEnvelope grade firstDerivative *
          coefficientEnvelope 0 (secondCurve t - secondCurve 0) +
        coefficientEnvelope 0 firstDerivative *
          coefficientEnvelope grade (secondCurve t - secondCurve 0)))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have shape := (((second.tendsto_difference 0).const_mul
        (coefficientEnvelope grade firstDerivative)).add
      ((second.tendsto_difference grade).const_mul
        (coefficientEnvelope 0 firstDerivative))).const_mul ((2 : ℝ) ^ grade)
    simpa using shape
  have termThree : Tendsto (fun t : ℝ => (2 : ℝ) ^ grade *
      (coefficientEnvelope grade (firstCurve 0) * coefficientEnvelope 0 (quotientTwo t) +
        coefficientEnvelope 0 (firstCurve 0) * coefficientEnvelope grade (quotientTwo t)))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have shape := (((second 0).const_mul (coefficientEnvelope grade (firstCurve 0))).add
      ((second grade).const_mul (coefficientEnvelope 0 (firstCurve 0)))).const_mul
      ((2 : ℝ) ^ grade)
    simpa using shape
  have total := (termOne.add termTwo).add termThree
  rw [add_zero, add_zero] at total
  exact squeeze_zero'
    (Eventually.of_forall (fun _ => coefficientEnvelope_nonneg _ _)) majorized total

/-- Erase-products through the `succAbove` embedding. -/
theorem prod_succAbove_eq_erase {arity : ℕ} (index : Fin (arity + 1))
    (values : Fin (arity + 1) → TameCoefficient parameters) :
    ∏ position : Fin arity, values (index.succAbove position) =
      ∏ other ∈ Finset.univ.erase index, values other := by
  rw [← Finset.compl_singleton, ← Fin.image_succAbove_univ index]
  rw [Finset.prod_image (fun _ _ _ _ equal => Fin.succAbove_right_injective equal)]

/-- Derivative-side congruence. -/
theorem HasEnvDerivAt.congr_derivative {curve : ℝ → TameCoefficient parameters}
    {firstDerivative secondDerivative : TameCoefficient parameters}
    (differentiable : HasEnvDerivAt curve firstDerivative)
    (agree : firstDerivative = secondDerivative) : HasEnvDerivAt curve secondDerivative := by
  rw [← agree]
  exact differentiable

/-- The finite product rule in the `succAbove` form. -/
theorem hasEnvDerivAt_prod_succAbove : ∀ {arity : ℕ}
    (curves : Fin (arity + 1) → ℝ → TameCoefficient parameters)
    (derivatives : Fin (arity + 1) → TameCoefficient parameters),
    (∀ index, HasEnvDerivAt (curves index) (derivatives index)) →
    HasEnvDerivAt (fun t => ∏ index, curves index t)
      (∑ index, derivatives index *
        ∏ position : Fin arity, curves (index.succAbove position) 0) := by
  intro arity
  induction arity with
  | zero =>
    intro curves derivatives differentiable
    have derivative_eq : (∑ index : Fin 1, derivatives index *
        ∏ position : Fin 0, curves (index.succAbove position) 0) = derivatives 0 := by
      rw [Fin.sum_univ_one, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    rw [derivative_eq]
    exact (differentiable 0).congr_curve
      (fun t => Fin.prod_univ_one (fun index => curves index t))
  | succ smaller inductive_step =>
    intro curves derivatives differentiable
    have head := differentiable 0
    have tail := inductive_step (fun index => curves index.succ)
      (fun index => derivatives index.succ) (fun index => differentiable index.succ)
    have combined := head.mul tail
    have relabeled := combined.congr_curve
      (fun t => Fin.prod_univ_succ (fun index => curves index t))
    apply relabeled.congr_derivative
    -- Identify the produced derivative with the succAbove form.
    conv_rhs => rw [Fin.sum_univ_succ]
    have head_eq : derivatives 0 * (∏ index : Fin (smaller + 1), curves index.succ 0) =
        derivatives 0 * ∏ position : Fin (smaller + 1),
          curves ((0 : Fin (smaller + 2)).succAbove position) 0 := by
      congr 1
    have tail_eq : curves 0 0 * (∑ index : Fin (smaller + 1), derivatives index.succ *
          ∏ position : Fin smaller, curves ((index.succAbove position).succ) 0) =
        ∑ index : Fin (smaller + 1), derivatives index.succ *
          ∏ position : Fin (smaller + 1), curves (index.succ.succAbove position) 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro index _
      have factor_split : (∏ inner : Fin (smaller + 1),
          curves (index.succ.succAbove inner) 0) =
          curves 0 0 * ∏ inner : Fin smaller,
            curves ((index.succAbove inner).succ) 0 := by
        rw [Fin.prod_univ_succ]
        have zero_factor : curves (index.succ.succAbove 0) 0 = curves 0 0 := by
          rw [Fin.succ_succAbove_zero]
        have tail_factor : ∀ inner : Fin smaller,
            curves (index.succ.succAbove inner.succ) 0 =
              curves ((index.succAbove inner).succ) 0 := by
          intro inner
          rw [Fin.succ_succAbove_succ]
        rw [zero_factor]
        congr 1
        exact Finset.prod_congr rfl (fun inner _ => tail_factor inner)
      rw [factor_split]
      ring
    rw [head_eq, tail_eq]

/-- The finite product rule with erase-form derivative. -/
theorem hasEnvDerivAt_prod {arity : ℕ}
    (curves : Fin (arity + 1) → ℝ → TameCoefficient parameters)
    (derivatives : Fin (arity + 1) → TameCoefficient parameters)
    (differentiable : ∀ index, HasEnvDerivAt (curves index) (derivatives index)) :
    HasEnvDerivAt (fun t => ∏ index, curves index t)
      (∑ index, derivatives index *
        ∏ other ∈ Finset.univ.erase index, curves other 0) := by
  apply (hasEnvDerivAt_prod_succAbove curves derivatives differentiable).congr_derivative
  apply Finset.sum_congr rfl
  intro index _
  rw [prod_succAbove_eq_erase index (fun other => curves other 0)]

end Grad.NonlinearQuotientBounds
