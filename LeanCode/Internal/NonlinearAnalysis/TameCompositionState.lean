import TameChartGoal
import QuotientPolynomialFinal
import GaugeSliceBounds
import GaugeProjectionBounds

noncomputable section

set_option maxHeartbeats 1600000

open Filter
open scoped BigOperators Topology

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.Constraints

/-! # The fixed-reference Q21 inner map

The joint Q23 state `u = (ε, x)` with `‖u‖_q = |ε| + ‖x‖_{X^q}`, the literal
N5 fixed-reference transfer `x ↦ (τ, T_{M*,M_p} ṽ, s)` (the accepted N18
seed-slice transfer on the vector part, the axis and potential parts fixed),
the inner map `G(ε, x) = (ε, 𝒮_p(T x))` into the Q4 state, and its genuine
derivative family with the exact one-high bounds at every grade. -/

variable {parameters : PhaseParameters}

/-- The joint state `(ε, x)`: the scalar and the reference-slice chart state. -/
abbrev JointState (parameters : PhaseParameters) : Type := ℂ × ChartState parameters

/-- The joint norm `|ε| + ‖x‖_{X^q}`. -/
def jointNorm (grade : ℕ) (state : JointState parameters) : ℝ :=
  ‖state.1‖ + chartStateNorm grade state.2

theorem jointNorm_nonneg (grade : ℕ) (state : JointState parameters) :
    0 ≤ jointNorm grade state :=
  add_nonneg (norm_nonneg _) (chartStateNorm_nonneg _ _)

theorem jointNorm_mono {lower upper : ℕ} (gradeLe : lower ≤ upper)
    (state : JointState parameters) :
    jointNorm lower state ≤ jointNorm upper state :=
  add_le_add le_rfl (chartStateNorm_mono gradeLe state.2)

theorem norm_fst_le_jointNorm (grade : ℕ) (state : JointState parameters) :
    ‖state.1‖ ≤ jointNorm grade state := by
  have := chartStateNorm_nonneg grade state.2
  unfold jointNorm
  linarith

theorem chartStateNorm_snd_le_jointNorm (grade : ℕ) (state : JointState parameters) :
    chartStateNorm grade state.2 ≤ jointNorm grade state := by
  have := norm_nonneg state.1
  unfold jointNorm
  linarith

/-! ### Algebra of the Q4 state norm -/

theorem stateNorm_add_le (grade : ℕ) (first second : QuotientState parameters) :
    stateNorm grade (first + second) ≤ stateNorm grade first + stateNorm grade second := by
  unfold stateNorm
  have scalar := norm_add_le first.1 second.1
  have field := originalGradeNorm_add_le grade first.2.1 second.2.1
  have potential := originalGradeNorm_add_le grade first.2.2 second.2.2
  change ‖first.1 + second.1‖ + originalGradeNorm grade (first.2.1 + second.2.1) +
    originalGradeNorm grade (first.2.2 + second.2.2) ≤ _
  linarith

theorem stateNorm_smul (grade : ℕ) (scalar : ℂ) (state : QuotientState parameters) :
    stateNorm grade (scalar • state) = ‖scalar‖ * stateNorm grade state := by
  unfold stateNorm
  change ‖scalar * state.1‖ + originalGradeNorm grade (scalar • state.2.1) +
    originalGradeNorm grade (scalar • state.2.2) = _
  rw [norm_mul, originalGradeNorm_smul, originalGradeNorm_smul]
  ring

theorem stateNorm_zero (grade : ℕ) : stateNorm grade (0 : QuotientState parameters) = 0 := by
  unfold stateNorm
  change ‖(0 : ℂ)‖ + originalGradeNorm grade (0 : ACore parameters 3) +
    originalGradeNorm grade (0 : ACore parameters 1) = 0
  rw [norm_zero, originalGradeNorm_zero, originalGradeNorm_zero, add_zero, add_zero]

theorem stateNorm_neg (grade : ℕ) (state : QuotientState parameters) :
    stateNorm grade (-state) = stateNorm grade state := by
  unfold stateNorm
  change ‖-state.1‖ + originalGradeNorm grade (-state.2.1) +
    originalGradeNorm grade (-state.2.2) = _
  rw [norm_neg, originalGradeNorm_neg, originalGradeNorm_neg]

theorem stateNorm_sub_le (grade : ℕ) (first second : QuotientState parameters) :
    stateNorm grade (first - second) ≤ stateNorm grade first + stateNorm grade second := by
  rw [sub_eq_add_neg]
  exact (stateNorm_add_le grade first (-second)).trans (by rw [stateNorm_neg])

/-- The state norm is controlled by any nearby state plus the difference. -/
theorem stateNorm_le_stateNorm_add_sub (grade : ℕ) (first second : QuotientState parameters) :
    stateNorm grade first ≤ stateNorm grade second + stateNorm grade (first - second) := by
  have := stateNorm_add_le grade second (first - second)
  rw [add_sub_cancel] at this
  exact this

theorem abs_stateNorm_sub_le (grade : ℕ) (first second : QuotientState parameters) :
    |stateNorm grade first - stateNorm grade second| ≤ stateNorm grade (first - second) := by
  rw [abs_sub_le_iff]
  constructor
  · have := stateNorm_le_stateNorm_add_sub grade first second
    linarith
  · have := stateNorm_le_stateNorm_add_sub grade second first
    rw [← stateNorm_neg grade (second - first), neg_sub] at this
    linarith

/-- The Q4 state norm of a scalar/chart-output pair. -/
theorem stateNorm_pair (grade : ℕ) (scalar : ℂ) (output : ChartOutput parameters) :
    stateNorm grade ((scalar, output) : QuotientState parameters) =
      ‖scalar‖ + chartOutputNorm grade output := by
  unfold stateNorm chartOutputNorm
  ring

/-! ### Genuine directional derivatives on the joint state -/

/-- Genuine directional differentiability of a Q4-state-valued map on the joint
state, in every state grade norm at once. -/
def IsJointStateDirectionalDerivative
    (mapping : JointState parameters → QuotientState parameters)
    (base direction : JointState parameters) (derivative : QuotientState parameters) : Prop :=
  ∀ grade : ℕ, Tendsto (fun t : ℝ => stateNorm grade
      ((((t : ℂ))⁻¹ • (mapping (base + (t : ℂ) • direction) - mapping base)) - derivative))
    (𝓝[≠] (0 : ℝ)) (𝓝 0)

/-- Genuine directional differentiability of a rows-valued map on the joint
state, in every original grade norm at once. -/
def IsJointRowsDirectionalDerivative
    (mapping : JointState parameters → QuotientRows parameters)
    (base direction : JointState parameters) (derivative : QuotientRows parameters) : Prop :=
  ∀ grade : ℕ, Tendsto (fun t : ℝ => rowsGradeNorm grade
      ((((t : ℂ))⁻¹ • (mapping (base + (t : ℂ) • direction) - mapping base)) - derivative))
    (𝓝[≠] (0 : ℝ)) (𝓝 0)

/-! ### The literal fixed-reference transfer -/

/-- The fixed-reference transfer `x = (τ, ṽ, s) ↦ (τ, T_{M*,M_p} ṽ, s)`: the
accepted N18 seed-slice transfer from the reference seed to the moving seed on
the vector part, the axis and potential parts unchanged. -/
def referenceTransfer (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) :
    ChartState parameters →ₗ[ℂ] ChartState parameters :=
  (LinearMap.fst ℂ (TangentCoefficient parameters) (ACore parameters 3 × ACore parameters 1)).prod
    ((((Gauges.seedTransfer parameters reference insideR seed insideS).comp
        (LinearMap.fst ℂ (ACore parameters 3) (ACore parameters 1))).comp
        (LinearMap.snd ℂ (TangentCoefficient parameters) (ACore parameters 3 × ACore parameters 1))).prod
      ((LinearMap.snd ℂ (ACore parameters 3) (ACore parameters 1)).comp
        (LinearMap.snd ℂ (TangentCoefficient parameters) (ACore parameters 3 × ACore parameters 1))))

variable (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
  (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)

theorem referenceTransfer_apply (state : ChartState parameters) :
    referenceTransfer parameters reference insideR seed insideS state =
      (state.1, Gauges.seedTransfer parameters reference insideR seed insideS state.2.1,
        state.2.2) := rfl

theorem referenceTransfer_fst (state : ChartState parameters) :
    (referenceTransfer parameters reference insideR seed insideS state).1 = state.1 := rfl

/-- The literal Q13 axis condition only sees the axis data, which the transfer
leaves unchanged. -/
theorem referenceTransfer_axis (state : ChartState parameters) :
    ChartAxisCondition (referenceTransfer parameters reference insideR seed insideS state) ↔
      ChartAxisCondition state := Iff.rfl

/-- The transfer grade factor `1 + |c_q|`, at least one. -/
def transferGradeFactor (parameters : PhaseParameters) (reference seed : Seed.Parameters)
    (grade : ℕ) : ℝ :=
  1 + |Gauges.seedTransferGradeConstant parameters reference seed grade|

theorem one_le_transferGradeFactor (grade : ℕ) :
    1 ≤ transferGradeFactor parameters reference seed grade := by
  unfold transferGradeFactor
  have := abs_nonneg (Gauges.seedTransferGradeConstant parameters reference seed grade)
  linarith

theorem transferGradeFactor_nonneg (grade : ℕ) :
    0 ≤ transferGradeFactor parameters reference seed grade :=
  zero_le_one.trans (one_le_transferGradeFactor reference seed grade)

theorem originalGradeNorm_seedTransfer_le (grade : ℕ) (field : ACore parameters 3) :
    originalGradeNorm grade (Gauges.seedTransfer parameters reference insideR seed insideS field) ≤
      |Gauges.seedTransferGradeConstant parameters reference seed grade| *
        originalGradeNorm grade field := by
  unfold originalGradeNorm
  rw [Gauges.ofCoreLinear_norm_coordinates, Gauges.ofCoreLinear_norm_coordinates]
  exact (Gauges.seedTransfer_coordinates_bound parameters reference insideR seed insideS
    field).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))

/-- Same-grade bound of the transferred chart state. -/
theorem chartStateNorm_referenceTransfer_le (grade : ℕ) (state : ChartState parameters) :
    chartStateNorm grade (referenceTransfer parameters reference insideR seed insideS state) ≤
      transferGradeFactor parameters reference seed grade * chartStateNorm grade state := by
  rw [referenceTransfer_apply]
  unfold chartStateNorm transferGradeFactor
  have vector := originalGradeNorm_seedTransfer_le reference insideR seed insideS grade state.2.1
  have tangent := tangentNorm_nonneg (grade + 1) state.1
  have field := originalGradeNorm_nonnegative grade state.2.1
  have potential := originalGradeNorm_nonnegative grade state.2.2
  have absNonneg := abs_nonneg (Gauges.seedTransferGradeConstant parameters reference seed grade)
  change tangentNorm (grade + 1) state.1 +
    originalGradeNorm grade (Gauges.seedTransfer parameters reference insideR seed insideS
      state.2.1) + originalGradeNorm grade state.2.2 ≤ _
  nlinarith [mul_nonneg absNonneg tangent, mul_nonneg absNonneg potential]

/-! ### The inner map `G(ε, x) = (ε, 𝒮_p(T x))` and its derivative family -/

/-- The fixed-reference Q4 state `(ε, 𝒮_p(T_{M*,M_p} x))`. -/
def referenceState (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (state : JointState parameters) : QuotientState parameters :=
  (state.1, normalizedChart parameters seed insideS
    (referenceTransfer parameters reference insideR seed insideS state.2))

/-- The scalar component of the derivative family: the base scalar at order
zero, the direction scalar at order one, zero above. -/
def referenceScalar : (order : ℕ) → JointState parameters →
    (Fin order → JointState parameters) → ℂ
  | 0, state, _ => state.1
  | 1, _, directions => (directions 0).1
  | _ + 2, _, _ => 0

/-- The derivative family of the inner map: the scalar component and the
chart derivative family at the transferred base along the transferred
directions. -/
def referenceFamily (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (order : ℕ) (state : JointState parameters)
    (directions : Fin order → JointState parameters) : QuotientState parameters :=
  (referenceScalar order state directions,
    chartDerivativeFamily parameters seed insideS order
      (referenceTransfer parameters reference insideR seed insideS state.2)
      (fun position => referenceTransfer parameters reference insideR seed insideS
        (directions position).2))

theorem referenceFamily_zeroth (state : JointState parameters) :
    referenceFamily parameters reference insideR seed insideS 0 state
        (fun position => position.elim0) =
      referenceState parameters reference insideR seed insideS state := by
  unfold referenceFamily referenceState
  refine Prod.ext rfl ?_
  convert chartDerivativeFamily_zeroth parameters seed insideS
    (referenceTransfer parameters reference insideR seed insideS state.2) using 2

/-- Linearity of the transfer along a joint line. -/
theorem referenceTransfer_line (base direction : JointState parameters) (t : ℝ) :
    referenceTransfer parameters reference insideR seed insideS (base + (t : ℂ) • direction).2 =
      referenceTransfer parameters reference insideR seed insideS base.2 +
        (t : ℂ) • referenceTransfer parameters reference insideR seed insideS direction.2 := by
  rw [Prod.snd_add, Prod.smul_snd, map_add, map_smul]

/-- Genuineness of the inner family along the newest direction, at every
base whose axis data obeys the literal Q13 condition. -/
theorem referenceFamily_genuine (order : ℕ) (base : JointState parameters)
    (directions : Fin (order + 1) → JointState parameters)
    (axis : ChartAxisCondition base.2) :
    IsJointStateDirectionalDerivative
      (fun state => referenceFamily parameters reference insideR seed insideS order state
        (fun position => directions position.castSucc))
      base (directions (Fin.last order))
      (referenceFamily parameters reference insideR seed insideS (order + 1) base directions) := by
  intro grade
  have chart := chartDerivativeFamily_genuine parameters seed insideS order
    (referenceTransfer parameters reference insideR seed insideS base.2)
    (fun position => referenceTransfer parameters reference insideR seed insideS
      (directions position).2)
    ((referenceTransfer_axis reference insideR seed insideS base.2).mpr axis) grade
  have scalar_zero : ∀ t : ℝ, t ≠ 0 →
      ((t : ℂ))⁻¹ * (referenceScalar order (base + (t : ℂ) • directions (Fin.last order))
          (fun position => directions position.castSucc) -
        referenceScalar order base (fun position => directions position.castSucc)) -
        referenceScalar (order + 1) base directions = 0 := by
    intro t nonzero
    have tC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nonzero
    rcases order with _ | _ | order
    · show ((t : ℂ))⁻¹ * ((base + (t : ℂ) • directions (Fin.last 0)).1 - base.1) -
        (directions 0).1 = 0
      rw [Prod.fst_add, Prod.smul_fst, smul_eq_mul, add_sub_cancel_left, ← mul_assoc,
        inv_mul_cancel₀ tC, one_mul]
      have : directions (Fin.last 0) = directions 0 := rfl
      rw [this, sub_self]
    · show ((t : ℂ))⁻¹ * ((directions (Fin.castSucc 0)).1 - (directions (Fin.castSucc 0)).1) -
        0 = 0
      rw [sub_self, mul_zero, sub_zero]
    · show ((t : ℂ))⁻¹ * ((0 : ℂ) - 0) - 0 = 0
      rw [sub_self, mul_zero, sub_zero]
  have expression : ∀ t : ℝ, t ≠ 0 →
      stateNorm grade ((((t : ℂ))⁻¹ • (referenceFamily parameters reference insideR seed insideS
          order (base + (t : ℂ) • directions (Fin.last order))
          (fun position => directions position.castSucc) -
        referenceFamily parameters reference insideR seed insideS order base
          (fun position => directions position.castSucc))) -
        referenceFamily parameters reference insideR seed insideS (order + 1) base directions) =
      chartOutputNorm grade ((((t : ℂ))⁻¹ • (chartDerivativeFamily parameters seed insideS order
          (referenceTransfer parameters reference insideR seed insideS base.2 +
            (t : ℂ) • referenceTransfer parameters reference insideR seed insideS
              (directions (Fin.last order)).2)
          (fun position => referenceTransfer parameters reference insideR seed insideS
            (directions position.castSucc).2) -
        chartDerivativeFamily parameters seed insideS order
          (referenceTransfer parameters reference insideR seed insideS base.2)
          (fun position => referenceTransfer parameters reference insideR seed insideS
            (directions position.castSucc).2))) -
        chartDerivativeFamily parameters seed insideS (order + 1)
          (referenceTransfer parameters reference insideR seed insideS base.2)
          (fun position => referenceTransfer parameters reference insideR seed insideS
            (directions position).2)) := by
    intro t nonzero
    have scalar := scalar_zero t nonzero
    unfold referenceFamily
    rw [referenceTransfer_line]
    change stateNorm grade
      ((((t : ℂ))⁻¹ * (referenceScalar order (base + (t : ℂ) • directions (Fin.last order))
          (fun position => directions position.castSucc) -
        referenceScalar order base (fun position => directions position.castSucc)) -
        referenceScalar (order + 1) base directions,
       ((t : ℂ))⁻¹ • (chartDerivativeFamily parameters seed insideS order
          (referenceTransfer parameters reference insideR seed insideS base.2 +
            (t : ℂ) • referenceTransfer parameters reference insideR seed insideS
              (directions (Fin.last order)).2)
          (fun position => referenceTransfer parameters reference insideR seed insideS
            (directions position.castSucc).2) -
        chartDerivativeFamily parameters seed insideS order
          (referenceTransfer parameters reference insideR seed insideS base.2)
          (fun position => referenceTransfer parameters reference insideR seed insideS
            (directions position.castSucc).2)) -
        chartDerivativeFamily parameters seed insideS (order + 1)
          (referenceTransfer parameters reference insideR seed insideS base.2)
          (fun position => referenceTransfer parameters reference insideR seed insideS
            (directions position).2)) : QuotientState parameters) = _
    rw [stateNorm_pair, scalar, norm_zero, zero_add]
  refine chart.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t nonzero
  exact (expression t nonzero).symm

/-! ### The one-high bound of the inner family -/

/-- The joint one-high expression: high grade on the base or on exactly one
direction, low grade on every other direction. -/
def jointOneHigh (high low : ℕ) {order : ℕ} (base : JointState parameters)
    (directions : Fin order → JointState parameters) : ℝ :=
  (1 + jointNorm high base) * ∏ position, jointNorm low (directions position) +
    ∑ position, jointNorm high (directions position) *
      ∏ other ∈ Finset.univ.erase position, jointNorm low (directions other)

theorem jointOneHigh_nonneg (high low : ℕ) {order : ℕ} (base : JointState parameters)
    (directions : Fin order → JointState parameters) :
    0 ≤ jointOneHigh high low base directions := by
  unfold jointOneHigh
  apply add_nonneg
  · exact mul_nonneg (by linarith [jointNorm_nonneg high base])
      (Finset.prod_nonneg fun _ _ => jointNorm_nonneg _ _)
  · exact Finset.sum_nonneg fun _ _ => mul_nonneg (jointNorm_nonneg _ _)
      (Finset.prod_nonneg fun _ _ => jointNorm_nonneg _ _)

theorem jointOneHigh_mono_high {high high' low : ℕ} (gradeLe : high ≤ high') {order : ℕ}
    (base : JointState parameters) (directions : Fin order → JointState parameters) :
    jointOneHigh high low base directions ≤ jointOneHigh high' low base directions := by
  unfold jointOneHigh
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (by linarith [jointNorm_mono gradeLe base])
      (Finset.prod_nonneg fun _ _ => jointNorm_nonneg _ _)
  · exact Finset.sum_le_sum fun position _ => mul_le_mul_of_nonneg_right
      (jointNorm_mono gradeLe _) (Finset.prod_nonneg fun _ _ => jointNorm_nonneg _ _)

/-- The scalar component is dominated by the joint one-high expression. -/
theorem norm_referenceScalar_le (high low : ℕ) (order : ℕ) (base : JointState parameters)
    (directions : Fin order → JointState parameters) :
    ‖referenceScalar order base directions‖ ≤ jointOneHigh high low base directions := by
  rcases order with _ | _ | order
  · show ‖base.1‖ ≤ _
    unfold jointOneHigh
    rw [Fin.prod_univ_zero, Fin.sum_univ_zero, mul_one, add_zero]
    have := norm_fst_le_jointNorm high base
    linarith
  · show ‖(directions 0).1‖ ≤ _
    unfold jointOneHigh
    have empty : (Finset.univ.erase (0 : Fin 1)) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro slot membership
      exact Finset.ne_of_mem_erase membership (Subsingleton.elim slot 0)
    rw [Fin.sum_univ_one, empty, Finset.prod_empty, mul_one]
    have first : 0 ≤ (1 + jointNorm high base) * ∏ position, jointNorm low (directions position) :=
      mul_nonneg (by linarith [jointNorm_nonneg high base])
        (Finset.prod_nonneg fun _ _ => jointNorm_nonneg _ _)
    have := norm_fst_le_jointNorm high (directions 0)
    linarith
  · show ‖(0 : ℂ)‖ ≤ _
    rw [norm_zero]
    exact jointOneHigh_nonneg high low base directions

/-- Products of transferred low norms against the joint low norms. -/
theorem prod_chartStateNorm_referenceTransfer_le (grade : ℕ) {order : ℕ}
    (directions : Fin order → JointState parameters) (subset : Finset (Fin order)) :
    ∏ position ∈ subset, chartStateNorm grade
        (referenceTransfer parameters reference insideR seed insideS (directions position).2) ≤
      transferGradeFactor parameters reference seed grade ^ order *
        ∏ position ∈ subset, jointNorm grade (directions position) := by
  have factorLe : 1 ≤ transferGradeFactor parameters reference seed grade :=
    one_le_transferGradeFactor reference seed grade
  calc ∏ position ∈ subset, chartStateNorm grade
        (referenceTransfer parameters reference insideR seed insideS (directions position).2)
      ≤ ∏ position ∈ subset, (transferGradeFactor parameters reference seed grade *
          jointNorm grade (directions position)) := by
        apply Finset.prod_le_prod (fun _ _ => chartStateNorm_nonneg _ _)
        intro position _
        exact (chartStateNorm_referenceTransfer_le reference insideR seed insideS grade _).trans
          (mul_le_mul_of_nonneg_left (chartStateNorm_snd_le_jointNorm grade _)
            (transferGradeFactor_nonneg reference seed grade))
    _ = transferGradeFactor parameters reference seed grade ^ subset.card *
          ∏ position ∈ subset, jointNorm grade (directions position) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
    _ ≤ transferGradeFactor parameters reference seed grade ^ order *
          ∏ position ∈ subset, jointNorm grade (directions position) := by
        apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun _ _ => jointNorm_nonneg _ _)
        apply pow_le_pow_right₀ factorLe
        exact (Finset.card_le_univ subset).trans (by rw [Fintype.card_fin])

/-- The inner family obeys the exact one-high bound at every grade, with the
same grade on both sides, on the literal Q13 axis ball. -/
theorem referenceFamily_bound (grade order : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : JointState parameters) (directions : Fin order → JointState parameters),
        ChartAxisCondition base.2 →
        stateNorm grade (referenceFamily parameters reference insideR seed insideS order
            base directions) ≤
          constant * jointOneHigh grade 4 base directions := by
  obtain ⟨chartC, chartC_nonneg, chartBound⟩ :=
    chartDerivativeFamily_bound parameters seed insideS grade order
  set K := transferGradeFactor parameters reference seed grade with K_def
  set K4 := transferGradeFactor parameters reference seed 4 with K4_def
  have K_one : 1 ≤ K := one_le_transferGradeFactor reference seed grade
  have K4_pow_nonneg : 0 ≤ K4 ^ order := pow_nonneg (transferGradeFactor_nonneg reference seed 4) _
  refine ⟨1 + chartC * (K * K4 ^ order), by positivity, ?_⟩
  intro base directions axis
  have expr_nonneg := jointOneHigh_nonneg grade 4 base directions
  have scalarPart := norm_referenceScalar_le grade 4 order base directions
  have chartPart : chartOutputNorm grade (chartDerivativeFamily parameters seed insideS order
      (referenceTransfer parameters reference insideR seed insideS base.2) (fun position => referenceTransfer parameters reference insideR seed insideS (directions position).2)) ≤
      chartC * (K * K4 ^ order) * jointOneHigh grade 4 base directions := by
    have applied := chartBound (referenceTransfer parameters reference insideR seed insideS base.2) (fun position => referenceTransfer parameters reference insideR seed insideS (directions position).2)
      ((referenceTransfer_axis reference insideR seed insideS base.2).mpr axis)
    refine applied.trans ?_
    rw [mul_assoc chartC]
    apply mul_le_mul_of_nonneg_left _ chartC_nonneg
    unfold jointOneHigh
    have baseFactor : 1 + chartStateNorm grade (referenceTransfer parameters reference insideR seed insideS base.2) ≤ K * (1 + jointNorm grade base) := by
      have := (chartStateNorm_referenceTransfer_le reference insideR seed insideS grade
        base.2).trans (mul_le_mul_of_nonneg_left (chartStateNorm_snd_le_jointNorm grade base)
          (transferGradeFactor_nonneg reference seed grade))
      have jn := jointNorm_nonneg grade base
      nlinarith
    have lowProduct := prod_chartStateNorm_referenceTransfer_le reference insideR seed insideS 4
      directions Finset.univ
    have firstTerm : (1 + chartStateNorm grade (referenceTransfer parameters reference insideR seed insideS base.2)) *
        ∏ position, chartStateNorm 4 (referenceTransfer parameters reference insideR seed insideS (directions position).2) ≤
        K * K4 ^ order * ((1 + jointNorm grade base) *
          ∏ position, jointNorm 4 (directions position)) := by
      have a_nonneg : 0 ≤ 1 + chartStateNorm grade (referenceTransfer parameters reference insideR seed insideS base.2) := by
        linarith [chartStateNorm_nonneg grade (referenceTransfer parameters reference insideR seed insideS base.2)]
      have b_nonneg : 0 ≤ K * (1 + jointNorm grade base) :=
        mul_nonneg (transferGradeFactor_nonneg reference seed grade)
          (by linarith [jointNorm_nonneg grade base])
      calc (1 + chartStateNorm grade (referenceTransfer parameters reference insideR seed insideS base.2)) *
            ∏ position, chartStateNorm 4 (referenceTransfer parameters reference insideR seed insideS (directions position).2)
          ≤ (K * (1 + jointNorm grade base)) *
              (K4 ^ order * ∏ position, jointNorm 4 (directions position)) :=
            mul_le_mul baseFactor lowProduct
              (Finset.prod_nonneg fun _ _ => chartStateNorm_nonneg _ _) b_nonneg
        _ = K * K4 ^ order * ((1 + jointNorm grade base) *
              ∏ position, jointNorm 4 (directions position)) := by ring
    have secondTerm : ∑ position, chartStateNorm grade (referenceTransfer parameters reference insideR seed insideS (directions position).2) *
        ∏ other ∈ Finset.univ.erase position, chartStateNorm 4 (referenceTransfer parameters reference insideR seed insideS (directions other).2) ≤
        K * K4 ^ order * ∑ position, jointNorm grade (directions position) *
          ∏ other ∈ Finset.univ.erase position, jointNorm 4 (directions other) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro position _
      have highFactor : chartStateNorm grade (referenceTransfer parameters reference insideR seed insideS (directions position).2) ≤
          K * jointNorm grade (directions position) :=
        (chartStateNorm_referenceTransfer_le reference insideR seed insideS grade _).trans
          (mul_le_mul_of_nonneg_left (chartStateNorm_snd_le_jointNorm grade _)
            (transferGradeFactor_nonneg reference seed grade))
      have lowFactor := prod_chartStateNorm_referenceTransfer_le reference insideR seed insideS 4
        directions (Finset.univ.erase position)
      calc chartStateNorm grade (referenceTransfer parameters reference insideR seed insideS (directions position).2) *
            ∏ other ∈ Finset.univ.erase position, chartStateNorm 4 (referenceTransfer parameters reference insideR seed insideS (directions other).2)
          ≤ (K * jointNorm grade (directions position)) *
              (K4 ^ order * ∏ other ∈ Finset.univ.erase position, jointNorm 4 (directions other)) :=
            mul_le_mul highFactor lowFactor
              (Finset.prod_nonneg fun _ _ => chartStateNorm_nonneg _ _)
              (mul_nonneg (transferGradeFactor_nonneg reference seed grade) (jointNorm_nonneg _ _))
        _ = K * K4 ^ order * (jointNorm grade (directions position) *
              ∏ other ∈ Finset.univ.erase position, jointNorm 4 (directions other)) := by ring
    calc (1 + chartStateNorm grade (referenceTransfer parameters reference insideR seed insideS base.2)) *
          ∏ position, chartStateNorm 4 (referenceTransfer parameters reference insideR seed insideS (directions position).2) +
        ∑ position, chartStateNorm grade (referenceTransfer parameters reference insideR seed insideS (directions position).2) *
          ∏ other ∈ Finset.univ.erase position, chartStateNorm 4 (referenceTransfer parameters reference insideR seed insideS (directions other).2)
        ≤ K * K4 ^ order * ((1 + jointNorm grade base) *
            ∏ position, jointNorm 4 (directions position)) +
          K * K4 ^ order * ∑ position, jointNorm grade (directions position) *
            ∏ other ∈ Finset.univ.erase position, jointNorm 4 (directions other) :=
          add_le_add firstTerm secondTerm
      _ = K * K4 ^ order * ((1 + jointNorm grade base) *
            ∏ position, jointNorm 4 (directions position) +
          ∑ position, jointNorm grade (directions position) *
            ∏ other ∈ Finset.univ.erase position, jointNorm 4 (directions other)) := by ring
  have split : (1 + chartC * (K * K4 ^ order)) * jointOneHigh grade 4 base directions =
      jointOneHigh grade 4 base directions +
        chartC * (K * K4 ^ order) * jointOneHigh grade 4 base directions := by ring
  unfold referenceFamily
  rw [stateNorm_pair, split]
  linarith

end Grad.NonlinearQuotientBounds
