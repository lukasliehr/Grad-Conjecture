import Q23SeedCoefficients
import GaugeSeedFamilies
import ProductSmoothSeries

noncomputable section

set_option maxHeartbeats 2400000

open Set Filter
open scoped BigOperators ContDiff ENNReal Topology

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.Constraints.Multipliers Grad.Constraints.Gauges Grad.Constraints.Seed
open Grad.GaugeCoefficients.Algebra

/-! Operator-level finite-seed calculus.  The output remains in the one
all-grade smooth core, while convergence is asserted in every original grade
norm. -/

theorem envelope_smul_summable (phase : PhaseParameters) (grade : ℕ)
    (scalar : ℂ) (coefficients : ℤ → OperatorValue 2 2)
    (summable : Summable (envelopeTerm phase grade coefficients)) :
    Summable (envelopeTerm phase grade (fun cell => scalar • coefficients cell)) := by
  have majorant := summable.mul_left ‖scalar‖
  apply majorant.congr
  intro cell
  unfold envelopeTerm
  rw [norm_smul]
  ring

theorem smoothMultiplier_smul_coefficients (phase : PhaseParameters)
    (scalar : ℂ) (coefficients : ℤ → OperatorValue 2 2)
    (summable : ∀ grade, Summable (envelopeTerm phase grade coefficients))
    (field : ACore phase 2) :
    smoothMultiplier phase (fun cell => scalar • coefficients cell)
        (fun grade => envelope_smul_summable phase grade scalar coefficients
          (summable grade)) field =
      scalar • smoothMultiplier phase coefficients summable field := by
  apply Subtype.ext
  funext cell
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have scaled := smoothMultiplier_value_hasSum phase _
    (fun grade => envelope_smul_summable phase grade scalar coefficients
      (summable grade)) field cell point
  have base := smoothMultiplier_value_hasSum phase coefficients summable field cell point
  have expected := base.const_smul scalar
  apply scaled.unique
  convert expected using 1
  · funext shift
    rfl
  · change ((scalar • (smoothMultiplier phase coefficients summable field).1 cell).value point) = _
    rw [closedJet_value_smul, ContinuousMap.smul_apply]

theorem envelope_sub_summable (phase : PhaseParameters) (grade : ℕ)
    (first second : ℤ → OperatorValue 2 2)
    (firstSummable : Summable (envelopeTerm phase grade first))
    (secondSummable : Summable (envelopeTerm phase grade second)) :
    Summable (envelopeTerm phase grade (fun cell => first cell - second cell)) := by
  apply Summable.of_nonneg_of_le
    (fun cell => envelopeTerm_nonnegative phase grade _ cell)
    (fun cell => ?_) (firstSummable.add secondSummable)
  unfold envelopeTerm
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_sub_le _ _)
    (mul_nonneg (Real.exp_pos _).le
      (pow_nonneg (zero_lt_one.trans_le (cellPolynomialWeight_one_le cell)).le _))

theorem smoothMultiplier_sub_coefficients (phase : PhaseParameters)
    (first second : ℤ → OperatorValue 2 2)
    (firstSummable : ∀ grade, Summable (envelopeTerm phase grade first))
    (secondSummable : ∀ grade, Summable (envelopeTerm phase grade second))
    (field : ACore phase 2) :
    smoothMultiplier phase (fun cell => first cell - second cell)
        (fun grade => envelope_sub_summable phase grade first second
          (firstSummable grade) (secondSummable grade)) field =
      smoothMultiplier phase first firstSummable field -
        smoothMultiplier phase second secondSummable field := by
  apply Subtype.ext
  funext cell
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have differenceSum := smoothMultiplier_value_hasSum phase _
    (fun grade => envelope_sub_summable phase grade first second
      (firstSummable grade) (secondSummable grade)) field cell point
  have expected := (smoothMultiplier_value_hasSum phase first firstSummable field cell point).sub
    (smoothMultiplier_value_hasSum phase second secondSummable field cell point)
  apply differenceSum.unique
  convert expected using 1
  · funext shift
    rfl
  · change ((smoothMultiplier phase first firstSummable field).1 cell -
      (smoothMultiplier phase second secondSummable field).1 cell).value point = _
    rw [sub_eq_add_neg, closedJet_value_add, ContinuousMap.add_apply,
      closedJet_value_neg, ContinuousMap.neg_apply, ← sub_eq_add_neg]

/-- Exact envelope/operator norm identity supplied by the weighted derivative
representation. -/
theorem seedCellParameterDerivative_envelope_eq_norm (phase : PhaseParameters)
    (grade order : ℕ) (kind : Fin 3) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) :
    envelope phase grade (seedCellParameterDerivative order kind parameter directions) =
      ‖iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind)
        parameter directions‖ := by
  rw [envelope, Seed.weightedSequence_norm]
  apply tsum_congr
  intro cell
  rw [weightedSeedFamilies_iteratedFDeriv_cell phase grade order kind parameter inside
    directions cell, Seed.weighted_norm]
  rfl

/-- The order-`j` seed derivative multiplier on the one all-grade core. -/
def seedParameterMultiplier (phase : PhaseParameters) (order : ℕ) (kind : Fin 3)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) :
    ACore phase 2 →ₗ[ℂ] ACore phase 2 :=
  smoothMultiplier phase (seedCellParameterDerivative order kind parameter directions)
    (fun grade => seedCellParameterDerivative_summable phase grade order kind parameter inside
      directions)

theorem seedParameterMultiplier_bound (phase : PhaseParameters) (grade order : ℕ)
    (kind : Fin 3) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) (field : ACore phase 2) :
    originalGradeNorm grade
        (seedParameterMultiplier phase order kind parameter inside directions field) ≤
      multiplierConstant grade phase.gamma *
        ‖iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind)
          parameter directions‖ * originalGradeNorm grade field := by
  have bound := smoothMultiplier_bound phase
    (seedCellParameterDerivative order kind parameter directions)
    (fun q => seedCellParameterDerivative_summable phase q order kind parameter inside
      directions) field grade
  rw [seedCellParameterDerivative_envelope_eq_norm phase grade order kind parameter inside
    directions] at bound
  exact bound

theorem seedParameterMultiplier_zero (phase : PhaseParameters) (kind : Fin 3)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (field : ACore phase 2) :
    seedParameterMultiplier phase 0 kind parameter inside (fun position => position.elim0)
        field =
      smoothMultiplier phase (Seed.actualCells kind parameter)
        (fun grade => seedCells_all_summable phase parameter inside kind grade) field := by
  rfl

/-- Totalized only outside the open seed domain; on that domain this is the
literal multiplier derivative.  Totalization makes a genuine line derivative
statement well-typed while proof irrelevance removes the domain witness. -/
def seedParameterMultiplierTotal (phase : PhaseParameters) (order : ℕ) (kind : Fin 3)
    (parameter : Seed.Parameters) (directions : Fin order → Seed.Parameters)
    (field : ACore phase 2) : ACore phase 2 := by
  classical
  exact if inside : parameter ∈ Seed.parameterDomain then
      seedParameterMultiplier phase order kind parameter inside directions field
    else 0

theorem seedParameterMultiplierTotal_of_inside (phase : PhaseParameters) (order : ℕ)
    (kind : Fin 3) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) (field : ACore phase 2) :
    seedParameterMultiplierTotal phase order kind parameter directions field =
      seedParameterMultiplier phase order kind parameter inside directions field := by
  classical
  simp only [seedParameterMultiplierTotal, dif_pos inside]

/-- A Fréchet derivative on a real line gives the punctured difference-quotient
limit in norm, in the exact complex-smul notation used by the smooth core. -/
theorem hasFDerivAt_real_quotient {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value]
    (curve : ℝ → Value) (derivative : Value) (h : HasFDerivAt curve
      ((ContinuousLinearMap.id ℝ ℝ).smulRight derivative) 0) :
    Tendsto (fun t : ℝ => ‖t⁻¹ • (curve t - curve 0) - derivative‖)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have little := h.isLittleO.norm_left
  have ratio : Tendsto (fun t : ℝ =>
      |‖curve t - curve 0 -
          ((ContinuousLinearMap.id ℝ ℝ).smulRight derivative) (t - 0)‖ / (t - 0)|)
      (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa using little.tendsto_div_nhds_zero.abs
  refine (ratio.mono_left nhdsWithin_le_nhds).congr' ?_
  apply eventually_nhdsWithin_of_forall
  intro t ht
  have realNonzero : t ≠ 0 := by simpa using ht
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, sub_zero]
  change |‖curve t - curve 0 - t • derivative‖ / t| =
    ‖t⁻¹ • (curve t - curve 0) - derivative‖
  symm
  have rearrange : t⁻¹ • (curve t - curve 0) - derivative =
      t⁻¹ • (curve t - curve 0 - t • derivative) := by
    calc
      t⁻¹ • (curve t - curve 0) - derivative =
          t⁻¹ • (curve t - curve 0) - t⁻¹ • (t • derivative) := by
        rw [smul_smul, inv_mul_cancel₀ realNonzero, one_smul]
      _ = _ := (smul_sub _ _ _).symm
  rw [rearrange, norm_smul, Real.norm_eq_abs, abs_inv, abs_div, abs_norm,
    div_eq_inv_mul]

/-- The accepted weighted seed family, evaluated on fixed old directions and
restricted to an affine seed line, has the literal next derivative. -/
theorem weightedSeed_line_hasFDerivAt (phase : PhaseParameters) (grade order : ℕ)
    (kind : Fin 3) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (oldDirections : Fin order → Seed.Parameters) (newDirection : Seed.Parameters) :
    HasFDerivAt
      (fun t : ℝ => iteratedFDeriv ℝ order
        (Seed.weightedSeedFamilies phase grade kind)
          (parameter + t • newDirection) oldDirections)
      ((ContinuousLinearMap.id ℝ ℝ).smulRight
        (iteratedFDeriv ℝ (order + 1)
          (Seed.weightedSeedFamilies phase grade kind) parameter
            (Fin.cons newDirection oldDirections))) 0 := by
  let evaluation := ContinuousMultilinearMap.apply ℝ
    (fun _ : Fin order => Seed.Parameters) WeightedSequence oldDirections
  have smoothAt :=
    (Seed.weightedSeedFamilies_contDiffOn phase grade kind).contDiffAt
      (Seed.parameterDomain_isOpen.mem_nhds inside)
  have derivativeAt : HasFDerivAt
      (iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind))
      (iteratedFDeriv ℝ (order + 1)
        (Seed.weightedSeedFamilies phase grade kind) parameter).curryLeft parameter := by
    have differentiable := smoothAt.differentiableAt_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl order)
    have result := differentiable.hasFDerivAt
    rw [fderiv_iteratedFDeriv, Function.comp_apply] at result
    exact result
  have evaluated := evaluation.hasFDerivAt.comp parameter derivativeAt
  let lineMap : ℝ →L[ℝ] Seed.Parameters :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight newDirection
  have lineDerivative : HasFDerivAt (fun t : ℝ => parameter + lineMap t) lineMap 0 := by
    have raw := (hasFDerivAt_const (x := (0 : ℝ)) parameter).add lineMap.hasFDerivAt
    exact raw.congr_fderiv (zero_add lineMap)
  have evaluatedAtLine : HasFDerivAt
      (evaluation ∘ iteratedFDeriv ℝ order
        (Seed.weightedSeedFamilies phase grade kind))
      (evaluation.comp
        (iteratedFDeriv ℝ (order + 1)
          (Seed.weightedSeedFamilies phase grade kind) parameter).curryLeft)
      (parameter + lineMap 0) := by
    simpa [lineMap] using evaluated
  have composed := evaluatedAtLine.comp 0 lineDerivative
  have derivativeEquality :
      (evaluation.comp
          (iteratedFDeriv ℝ (order + 1)
            (Seed.weightedSeedFamilies phase grade kind) parameter).curryLeft).comp lineMap =
        (ContinuousLinearMap.id ℝ ℝ).smulRight
          (iteratedFDeriv ℝ (order + 1)
            (Seed.weightedSeedFamilies phase grade kind) parameter
              (Fin.cons newDirection oldDirections)) := by
    apply ContinuousLinearMap.ext
    intro scalar
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply]
    dsimp [evaluation, lineMap]
    let derivative := iteratedFDeriv ℝ (order + 1)
      (Seed.weightedSeedFamilies phase grade kind) parameter
    change (derivative.curryLeft (scalar • newDirection)) oldDirections =
      scalar • (derivative.curryLeft newDirection) oldDirections
    rw [map_smul, smul_apply]
  have adjusted := composed.congr_fderiv derivativeEquality
  apply adjusted.congr_of_eventuallyEq
  · filter_upwards [] with t
    rfl

/-- Genuine all-order finite-seed derivatives of the actual multiplier, in
every original grade norm.  The newest direction is inserted first, matching
Mathlib's `curryLeft` convention. -/
theorem seedParameterMultiplier_genuine (phase : PhaseParameters) (order : ℕ)
    (kind : Fin 3) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (oldDirections : Fin order → Seed.Parameters) (newDirection : Seed.Parameters)
    (field : ACore phase 2) (grade : ℕ) :
    Tendsto (fun t : ℝ => originalGradeNorm grade
      ((((t : ℂ))⁻¹ •
          (seedParameterMultiplierTotal phase order kind
              (parameter + t • newDirection) oldDirections field -
            seedParameterMultiplierTotal phase order kind parameter oldDirections field)) -
        seedParameterMultiplierTotal phase (order + 1) kind parameter
          (Fin.cons newDirection oldDirections) field))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have lineTendsto : Tendsto (fun t : ℝ => parameter + t • newDirection)
      (𝓝 (0 : ℝ)) (𝓝 parameter) := by
    have continuousLine : Continuous (fun t : ℝ => parameter + t • newDirection) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa only [ContinuousAt, zero_smul, add_zero] using
      (continuousLine.continuousAt : Tendsto (fun t : ℝ => parameter + t • newDirection)
        (𝓝 (0 : ℝ)) (𝓝 (parameter + (0 : ℝ) • newDirection)))
  have nearInsideFull : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
      parameter + t • newDirection ∈ Seed.parameterDomain :=
    lineTendsto.eventually (Seed.parameterDomain_isOpen.mem_nhds inside)
  have nearInside : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      parameter + t • newDirection ∈ Seed.parameterDomain :=
    nearInsideFull.filter_mono nhdsWithin_le_nhds
  have weightedLimitReal := hasFDerivAt_real_quotient _ _
    (weightedSeed_line_hasFDerivAt phase grade order kind parameter inside oldDirections
      newDirection)
  have weightedLimit : Tendsto (fun t : ℝ =>
      ‖(((t : ℂ))⁻¹ •
          (iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind)
              (parameter + t • newDirection) oldDirections -
            iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind)
              parameter oldDirections)) -
        iteratedFDeriv ℝ (order + 1) (Seed.weightedSeedFamilies phase grade kind)
          parameter (Fin.cons newDirection oldDirections)‖)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    refine weightedLimitReal.congr' (Eventually.of_forall (fun t => ?_))
    rw [zero_smul, add_zero]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    change ‖((t⁻¹ : ℝ) : ℂ) • _ - _‖ = ‖((t : ℂ)⁻¹) • _ - _‖
    rw [Complex.ofReal_inv]
  apply squeeze_zero'
    (Eventually.of_forall (fun _ => originalGradeNorm_nonnegative _ _))
    (g := fun t : ℝ => multiplierConstant grade phase.gamma *
      ‖(((t : ℂ))⁻¹ •
          (iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind)
              (parameter + t • newDirection) oldDirections -
            iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind)
              parameter oldDirections)) -
        iteratedFDeriv ℝ (order + 1) (Seed.weightedSeedFamilies phase grade kind)
          parameter (Fin.cons newDirection oldDirections)‖ *
        originalGradeNorm grade field) ?_ ?_
  · filter_upwards [nearInside] with t insideLine
    rw [seedParameterMultiplierTotal_of_inside phase order kind
      (parameter + t • newDirection) insideLine oldDirections field,
      seedParameterMultiplierTotal_of_inside phase order kind parameter inside
        oldDirections field,
      seedParameterMultiplierTotal_of_inside phase (order + 1) kind parameter inside
        (Fin.cons newDirection oldDirections) field]
    let first := seedCellParameterDerivative order kind
      (parameter + t • newDirection) oldDirections
    let second := seedCellParameterDerivative order kind parameter oldDirections
    let next := seedCellParameterDerivative (order + 1) kind parameter
      (Fin.cons newDirection oldDirections)
    let difference := fun cell => ((t : ℂ))⁻¹ • (first cell - second cell) - next cell
    have firstSummable := fun q => seedCellParameterDerivative_summable phase q order kind
      (parameter + t • newDirection) insideLine oldDirections
    have secondSummable := fun q => seedCellParameterDerivative_summable phase q order kind
      parameter inside oldDirections
    have nextSummable := fun q => seedCellParameterDerivative_summable phase q (order + 1) kind
      parameter inside (Fin.cons newDirection oldDirections)
    have differenceSummable : ∀ q, Summable (envelopeTerm phase q difference) :=
      fun q => envelope_sub_summable phase q
        (fun cell => ((t : ℂ))⁻¹ • (first cell - second cell)) next
        (envelope_smul_summable phase q ((t : ℂ))⁻¹
          (fun cell => first cell - second cell)
          (envelope_sub_summable phase q first second
            (firstSummable q) (secondSummable q))) (nextSummable q)
    have outputEq :
        (((t : ℂ))⁻¹ •
            (seedParameterMultiplier phase order kind (parameter + t • newDirection)
                insideLine oldDirections field -
              seedParameterMultiplier phase order kind parameter inside oldDirections field)) -
          seedParameterMultiplier phase (order + 1) kind parameter inside
            (Fin.cons newDirection oldDirections) field =
        smoothMultiplier phase difference differenceSummable field := by
      change ((t : ℂ))⁻¹ •
          (smoothMultiplier phase first firstSummable field -
            smoothMultiplier phase second secondSummable field) -
          smoothMultiplier phase next nextSummable field = _
      rw [← smoothMultiplier_sub_coefficients phase first second firstSummable secondSummable field]
      rw [← smoothMultiplier_smul_coefficients phase ((t : ℂ))⁻¹
        (fun cell => first cell - second cell)
        (fun q => envelope_sub_summable phase q first second
          (firstSummable q) (secondSummable q)) field]
      rw [← smoothMultiplier_sub_coefficients phase
        (fun cell => ((t : ℂ))⁻¹ • (first cell - second cell)) next
        (fun q => envelope_smul_summable phase q ((t : ℂ))⁻¹
          (fun cell => first cell - second cell)
          (envelope_sub_summable phase q first second
            (firstSummable q) (secondSummable q))) nextSummable field]
    rw [outputEq]
    have bound := smoothMultiplier_bound phase difference differenceSummable field grade
    calc originalGradeNorm grade (smoothMultiplier phase difference _ field)
        ≤ multiplierConstant grade phase.gamma * envelope phase grade difference *
            originalGradeNorm grade field := bound
      _ = multiplierConstant grade phase.gamma *
          ‖(((t : ℂ))⁻¹ •
              (iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind)
                  (parameter + t • newDirection) oldDirections -
                iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind)
                  parameter oldDirections)) -
            iteratedFDeriv ℝ (order + 1)
              (Seed.weightedSeedFamilies phase grade kind) parameter
                (Fin.cons newDirection oldDirections)‖ * originalGradeNorm grade field := by
        congr 2
        rw [envelope, Seed.weightedSequence_norm]
        apply tsum_congr
        intro cell
        change envelopeTerm phase grade difference cell =
          ‖((t : ℂ))⁻¹ •
              ((iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind)
                  (parameter + t • newDirection) oldDirections) cell -
                (iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind)
                  parameter oldDirections) cell) -
            (iteratedFDeriv ℝ (order + 1)
              (Seed.weightedSeedFamilies phase grade kind) parameter
                (Fin.cons newDirection oldDirections)) cell‖
        rw [weightedSeedFamilies_iteratedFDeriv_cell phase grade order kind
          (parameter + t • newDirection) insideLine oldDirections cell,
          weightedSeedFamilies_iteratedFDeriv_cell phase grade order kind parameter inside
            oldDirections cell,
          weightedSeedFamilies_iteratedFDeriv_cell phase grade (order + 1) kind parameter inside
            (Fin.cons newDirection oldDirections) cell]
        unfold difference first second next
        have weightedRemainder :
            ((t : ℂ))⁻¹ •
                ((sequenceWeight phase grade cell : ℂ) •
                    seedCellParameterDerivative order kind
                      (parameter + t • newDirection) oldDirections cell -
                  (sequenceWeight phase grade cell : ℂ) •
                    seedCellParameterDerivative order kind parameter oldDirections cell) -
              (sequenceWeight phase grade cell : ℂ) •
                seedCellParameterDerivative (order + 1) kind parameter
                  (Fin.cons newDirection oldDirections) cell =
            (sequenceWeight phase grade cell : ℂ) •
              (((t : ℂ))⁻¹ •
                  (seedCellParameterDerivative order kind
                      (parameter + t • newDirection) oldDirections cell -
                    seedCellParameterDerivative order kind parameter oldDirections cell) -
                seedCellParameterDerivative (order + 1) kind parameter
                  (Fin.cons newDirection oldDirections) cell) := by
          module
        rw [weightedRemainder, Seed.weighted_norm]
        rfl
  · have limit := (weightedLimit.const_mul
      (multiplierConstant grade phase.gamma)).mul_const (originalGradeNorm grade field)
    simpa using limit

end Grad.NonlinearQuotientBounds
