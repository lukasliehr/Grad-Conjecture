import TameRootDerivative

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! The tangential coefficient space of the normalized chart: the literal
M16 axis-weight norms `‖a‖_{T^q}² = Σ e^{2σ₀λ} λ^{2q} ‖a_n‖²`, the exact
`Σ λ⁻² ≤ 1 + π` axis estimate, and the M17/Q12 Cauchy–Schwarz bridge from
the `ℓ¹` planar envelope to the tangential norm with the literal constant
`√2^s √(1+π)`. -/

variable {parameters : PhaseParameters}

/-- One M16 summand `e^{2σ₀λ} λ^{2 grade} ‖τ_cell‖²`. -/
def tangentNormTerm (parameters : PhaseParameters) (grade : ℕ)
    (family : ℤ → ComplexEuclidean 2) (cell : ℤ) : ℝ :=
  Real.exp (parameters.sigma0 * cellFrequency cell) ^ 2 *
    cellFrequency cell ^ (2 * grade) * ‖family cell‖ ^ 2

theorem tangentNormTerm_nonneg (grade : ℕ) (family : ℤ → ComplexEuclidean 2) (cell : ℤ) :
    0 ≤ tangentNormTerm parameters grade family cell := by
  have freq_pos : 0 < cellFrequency cell := Grad.CellWeights.cellWeight_pos cell
  rw [tangentNormTerm]
  exact mul_nonneg (mul_nonneg (pow_nonneg (Real.exp_pos _).le 2)
    (pow_nonneg freq_pos.le _)) (pow_nonneg (norm_nonneg _) 2)

/-- All-grade finiteness of the M16 norms. -/
def TangentSummableFamily (parameters : PhaseParameters)
    (family : ℤ → ComplexEuclidean 2) : Prop :=
  ∀ grade : ℕ, Summable (tangentNormTerm parameters grade family)

/-- The tangential coefficient core as a complex submodule. -/
def tangentCoefficientSubmodule (parameters : PhaseParameters) :
    Submodule ℂ (ℤ → ComplexEuclidean 2) where
  carrier := {family | TangentSummableFamily parameters family}
  zero_mem' := by
    intro grade
    apply summable_zero.congr
    intro cell
    simp [tangentNormTerm]
  add_mem' := by
    intro first second firstSummable secondSummable grade
    apply Summable.of_nonneg_of_le (tangentNormTerm_nonneg grade _)
      (fun cell => ?_) (((firstSummable grade).add (secondSummable grade)).mul_left 2)
    have square_bound : ‖(first + second) cell‖ ^ 2 ≤
        2 * (‖first cell‖ ^ 2 + ‖second cell‖ ^ 2) := by
      have triangle : ‖(first + second) cell‖ ≤ ‖first cell‖ + ‖second cell‖ := by
        rw [Pi.add_apply]
        exact norm_add_le _ _
      have expand : (‖first cell‖ + ‖second cell‖) ^ 2 ≤
          2 * (‖first cell‖ ^ 2 + ‖second cell‖ ^ 2) := by
        nlinarith [sq_nonneg (‖first cell‖ - ‖second cell‖), norm_nonneg (first cell),
          norm_nonneg (second cell)]
      calc ‖(first + second) cell‖ ^ 2
          ≤ (‖first cell‖ + ‖second cell‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) triangle 2
        _ ≤ _ := expand
    calc tangentNormTerm parameters grade (first + second) cell
        = Real.exp (parameters.sigma0 * cellFrequency cell) ^ 2 *
            cellFrequency cell ^ (2 * grade) * ‖(first + second) cell‖ ^ 2 := rfl
      _ ≤ Real.exp (parameters.sigma0 * cellFrequency cell) ^ 2 *
            cellFrequency cell ^ (2 * grade) *
            (2 * (‖first cell‖ ^ 2 + ‖second cell‖ ^ 2)) := by
          apply mul_le_mul_of_nonneg_left square_bound
          have freq_pos : 0 < cellFrequency cell := Grad.CellWeights.cellWeight_pos cell
          exact mul_nonneg (pow_nonneg (Real.exp_pos _).le 2) (pow_nonneg freq_pos.le _)
      _ = 2 * (tangentNormTerm parameters grade first cell +
            tangentNormTerm parameters grade second cell) := by
          rw [tangentNormTerm, tangentNormTerm]
          ring
  smul_mem' := by
    intro scalar family familySummable grade
    apply ((familySummable grade).mul_left (‖scalar‖ ^ 2)).congr
    intro cell
    calc ‖scalar‖ ^ 2 * tangentNormTerm parameters grade family cell
        = Real.exp (parameters.sigma0 * cellFrequency cell) ^ 2 *
            cellFrequency cell ^ (2 * grade) * (‖scalar‖ ^ 2 * ‖family cell‖ ^ 2) := by
          rw [tangentNormTerm]
          ring
      _ = tangentNormTerm parameters grade (scalar • family) cell := by
          rw [tangentNormTerm]
          congr 1
          rw [Pi.smul_apply, norm_smul, mul_pow]

/-- The tangential coefficient carrier. -/
abbrev TangentCoefficient (parameters : PhaseParameters) : Type :=
  tangentCoefficientSubmodule parameters

theorem tangentCoefficient_summable (family : TangentCoefficient parameters) :
    TangentSummableFamily parameters family.val := family.property

/-- The literal M16 tangential norm at one grade. -/
def tangentNorm (grade : ℕ) (family : TangentCoefficient parameters) : ℝ :=
  Real.sqrt (∑' cell, tangentNormTerm parameters grade family.val cell)

theorem tangentNorm_nonneg (grade : ℕ) (family : TangentCoefficient parameters) :
    0 ≤ tangentNorm grade family := Real.sqrt_nonneg _

/-- The literal axis constant `C_ax = √(1 + π)`. -/
def axisConstant : ℝ := Real.sqrt (1 + Real.pi)

/-- The elementary bound `3 < π` through the cosine double angle. -/
theorem tame_three_lt_pi : (3 : ℝ) < Real.pi := by
  have half_bound : (23 / 32 : ℝ) ≤ Real.cos (3 / 4) := by
    have quadratic := Real.one_sub_sq_div_two_le_cos (x := (3 / 4 : ℝ))
    norm_num at quadratic
    linarith
  have double : Real.cos (2 * (3 / 4)) = 2 * Real.cos (3 / 4) ^ 2 - 1 :=
    Real.cos_two_mul (3 / 4)
  have angle_eq : (2 : ℝ) * (3 / 4) = 3 / 2 := by norm_num
  rw [angle_eq] at double
  have positive : 0 < Real.cos (3 / 2) := by
    have square_bound : (23 / 32 : ℝ) ^ 2 ≤ Real.cos (3 / 4) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) half_bound 2
    rw [double]
    nlinarith
  by_contra pi_small
  rw [not_lt] at pi_small
  have half_le : Real.pi / 2 ≤ 3 / 2 := by linarith
  have upper : (3 / 2 : ℝ) ≤ Real.pi + Real.pi / 2 := by
    have := Real.two_le_pi
    linarith
  have nonpos := Real.cos_nonpos_of_pi_div_two_le_of_le half_le upper
  linarith

/-! ### The `Σ λ⁻² ≤ 1 + π` axis estimate -/

/-- The telescoping tail bound `Σ_{k} ((k+1)(k+2))⁻¹ = 1`. -/
theorem telescoping_hasSum :
    HasSum (fun k : ℕ => (((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ))⁻¹) 1 := by
  have term_eq : ∀ k : ℕ, (((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ))⁻¹ =
      ((k + 1 : ℕ) : ℝ)⁻¹ - ((k + 2 : ℕ) : ℝ)⁻¹ := by
    intro k
    have first_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have second_pos : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
    rw [eq_sub_iff_add_eq]
    field_simp
    push_cast
    ring
  have partial_eq : ∀ count : ℕ, (∑ k ∈ Finset.range count,
      (((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ))⁻¹) = 1 - ((count + 1 : ℕ) : ℝ)⁻¹ := by
    intro count
    induction count with
    | zero => simp
    | succ smaller inductive_step =>
      rw [Finset.sum_range_succ, inductive_step, term_eq]
      push_cast
      ring
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun k => by positivity) 1).mpr
  have rewrite : (fun count : ℕ => ∑ k ∈ Finset.range count,
      (((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ))⁻¹) =
      fun count : ℕ => 1 - ((count + 1 : ℕ) : ℝ)⁻¹ := funext partial_eq
  rw [rewrite]
  have inverse_limit : Filter.Tendsto (fun count : ℕ => ((count + 1 : ℕ) : ℝ)⁻¹)
      Filter.atTop (nhds 0) := by
    have cast_limit := tendsto_natCast_atTop_atTop (R := ℝ)
    have shifted : Filter.Tendsto (fun count : ℕ => ((count + 1 : ℕ) : ℝ))
        Filter.atTop Filter.atTop := by
      apply Filter.Tendsto.comp cast_limit
      exact Filter.tendsto_add_atTop_nat 1
    exact shifted.inv_tendsto_atTop
  have shape := (tendsto_const_nhds (x := (1 : ℝ))
    (f := Filter.atTop (α := ℕ))).sub inverse_limit
  simpa using shape

/-- The natural tail comparison majorant. -/
def naturalTailBound (k : ℕ) : ℝ :=
  match k with
  | 0 => 1 / 2
  | k + 1 => (((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ))⁻¹

theorem naturalTailBound_nonneg (k : ℕ) : 0 ≤ naturalTailBound k := by
  match k with
  | 0 =>
    rw [naturalTailBound]
    norm_num
  | k + 1 =>
    rw [naturalTailBound]
    positivity

theorem naturalTailBound_hasSum : HasSum naturalTailBound (3 / 2) := by
  have shifted : HasSum (fun k : ℕ => naturalTailBound (k + 1)) 1 := telescoping_hasSum
  have total := (hasSum_nat_add_iff (f := naturalTailBound) 1).mp shifted
  have value : (1 : ℝ) + ∑ i ∈ Finset.range 1, naturalTailBound i = 3 / 2 := by
    rw [Finset.sum_range_one]
    rw [show naturalTailBound 0 = 1 / 2 from rfl]
    norm_num
  rw [value] at total
  exact total

theorem naturalTailBound_summable : Summable naturalTailBound :=
  naturalTailBound_hasSum.summable

theorem naturalTailBound_tsum : (∑' k, naturalTailBound k) = 3 / 2 :=
  naturalTailBound_hasSum.tsum_eq

/-- Tail comparison against the telescoping majorant. -/
theorem tail_le_naturalTailBound (k : ℕ) :
    ((1 : ℝ) + ((k + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤ naturalTailBound k := by
  match k with
  | 0 =>
    rw [naturalTailBound]
    norm_num
  | k + 1 =>
    rw [naturalTailBound]
    have product_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) := by positivity
    have product_le : ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) ≤
        (1 : ℝ) + ((k + 1 + 1 : ℕ) : ℝ) ^ 2 := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le product_pos product_le

/-- The inverse-square frequency family over the cells. -/
def inverseSquareFrequency (cell : ℤ) : ℝ := (cellFrequency cell ^ 2)⁻¹

theorem inverseSquareFrequency_eq (cell : ℤ) :
    inverseSquareFrequency cell = ((1 : ℝ) + (cell : ℝ) ^ 2)⁻¹ := by
  rw [inverseSquareFrequency, cellFrequency, Grad.CellBinomial.cellWeight_sq]

theorem inverseSquareFrequency_nonneg (cell : ℤ) : 0 ≤ inverseSquareFrequency cell := by
  rw [inverseSquareFrequency_eq]
  positivity

theorem inverseSquareFrequency_nat_le (k : ℕ) :
    inverseSquareFrequency ((k : ℤ) + 1) ≤ naturalTailBound k := by
  rw [inverseSquareFrequency_eq]
  have cast_eq : (((k : ℤ) + 1 : ℤ) : ℝ) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [cast_eq]
  exact tail_le_naturalTailBound k

theorem inverseSquareFrequency_neg_le (k : ℕ) :
    inverseSquareFrequency (-((k : ℤ) + 1)) ≤ naturalTailBound k := by
  rw [inverseSquareFrequency_eq]
  have cast_eq : ((-((k : ℤ) + 1) : ℤ) : ℝ) ^ 2 = ((k + 1 : ℕ) : ℝ) ^ 2 := by
    push_cast
    ring
  rw [cast_eq]
  exact tail_le_naturalTailBound k

theorem positive_side_summable :
    Summable (fun k : ℕ => inverseSquareFrequency ((k : ℤ) + 1)) :=
  Summable.of_nonneg_of_le (fun _ => inverseSquareFrequency_nonneg _)
    inverseSquareFrequency_nat_le naturalTailBound_summable

theorem negative_side_summable :
    Summable (fun k : ℕ => inverseSquareFrequency (-((k : ℤ) + 1))) :=
  Summable.of_nonneg_of_le (fun _ => inverseSquareFrequency_nonneg _)
    inverseSquareFrequency_neg_le naturalTailBound_summable

theorem nat_cast_side_summable :
    Summable (fun k : ℕ => inverseSquareFrequency (k : ℤ)) := by
  have shifted := positive_side_summable
  apply (summable_nat_add_iff 1).mp
  apply shifted.congr
  intro k
  congr 1

theorem neg_add_one_side_summable :
    Summable (fun k : ℕ => inverseSquareFrequency (-((k : ℤ) + 1))) :=
  negative_side_summable

/-- Summability of the axis weights. -/
theorem inverseSquareFrequency_summable : Summable inverseSquareFrequency :=
  (HasSum.of_nat_of_neg_add_one nat_cast_side_summable.hasSum
    neg_add_one_side_summable.hasSum).summable

/-- The literal axis estimate `Σ λ⁻² ≤ 1 + π`. -/
theorem inverseSquareFrequency_tsum_le :
    (∑' cell, inverseSquareFrequency cell) ≤ 1 + Real.pi := by
  have split := tsum_of_nat_of_neg_add_one
    (f := fun cell : ℤ => inverseSquareFrequency cell)
    nat_cast_side_summable neg_add_one_side_summable
  have positive_bound : (∑' k : ℕ, inverseSquareFrequency (k : ℤ)) ≤ 5 / 2 := by
    have zeroth : inverseSquareFrequency ((0 : ℕ) : ℤ) = 1 := by
      rw [inverseSquareFrequency_eq]
      norm_num
    have decomposition := nat_cast_side_summable.tsum_eq_zero_add
    rw [decomposition, zeroth]
    have tail_le : (∑' k : ℕ, inverseSquareFrequency ((k + 1 : ℕ) : ℤ)) ≤ 3 / 2 := by
      have comparison : ∀ k : ℕ, inverseSquareFrequency ((k + 1 : ℕ) : ℤ) ≤
          naturalTailBound k := by
        intro k
        have cast_eq : (((k + 1 : ℕ) : ℤ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
        rw [cast_eq]
        exact inverseSquareFrequency_nat_le k
      calc (∑' k : ℕ, inverseSquareFrequency ((k + 1 : ℕ) : ℤ))
          ≤ ∑' k, naturalTailBound k := by
            apply Summable.tsum_le_tsum comparison _ naturalTailBound_summable
            apply (summable_nat_add_iff 1).mpr nat_cast_side_summable |>.congr
            intro k
            rfl
        _ = 3 / 2 := naturalTailBound_tsum
    linarith
  have negative_bound : (∑' k : ℕ, inverseSquareFrequency (-((k : ℤ) + 1))) ≤ 3 / 2 := by
    calc (∑' k : ℕ, inverseSquareFrequency (-((k : ℤ) + 1)))
        ≤ ∑' k, naturalTailBound k :=
          Summable.tsum_le_tsum inverseSquareFrequency_neg_le
            negative_side_summable naturalTailBound_summable
      _ = 3 / 2 := naturalTailBound_tsum
  have pi_bound := tame_three_lt_pi
  calc (∑' cell, inverseSquareFrequency cell)
      = (∑' k : ℕ, inverseSquareFrequency (k : ℤ)) +
        ∑' k : ℕ, inverseSquareFrequency (-((k : ℤ) + 1)) := split
    _ ≤ 5 / 2 + 3 / 2 := add_le_add positive_bound negative_bound
    _ ≤ 1 + Real.pi := by linarith

end Grad.NonlinearQuotientBounds
