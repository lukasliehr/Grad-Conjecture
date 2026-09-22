import AOD1DifferentiatedEquation

noncomputable section
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff BigOperators
namespace Grad.CircularHighRegularity

/-- A finite envelope of the actual reciprocal derivatives in Leibniz' rule. -/
def reciprocalJetEnvelope (lower : ℝ) (order : ℕ) (radius : ℝ) : ℝ :=
  ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) *
    (‖iteratedDerivWithin index (fun radius : ℝ => radius⁻¹) (Icc lower 1) radius‖ +
      ‖iteratedDerivWithin index (fun radius : ℝ => radius⁻¹ ^ 2) (Icc lower 1) radius‖)

theorem reciprocalJetEnvelope_continuous (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (order : ℕ) : ContinuousOn (reciprocalJetEnvelope lower order) (Icc lower 1) := by
  have smooth : ContDiffOn ℝ ∞ (fun radius : ℝ => radius⁻¹) (Icc lower 1) :=
    contDiffOn_id.inv (fun radius inside => (positive.trans_le inside.1).ne')
  apply continuousOn_finsetSum
  intro index _
  have finite : (index : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (index : ℕ∞) ≤ ⊤)
  exact ((smooth.continuousOn_iteratedDerivWithin finite (uniqueDiffOn_Icc bounded)).norm.add
    ((smooth.pow 2).continuousOn_iteratedDerivWithin finite (uniqueDiffOn_Icc bounded)).norm).const_mul _

theorem exists_reciprocalJet_bound (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (order : ℕ) : ∃ bound : ℝ, 1 ≤ bound ∧ ∀ radius ∈ Icc lower 1,
      reciprocalJetEnvelope lower order radius ≤ bound := by
  obtain ⟨bound, property⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image (reciprocalJetEnvelope_continuous lower positive bounded order))
  refine ⟨max 1 bound, le_max_left _ _, ?_⟩
  intro radius inside
  exact (property _ ⟨radius, inside, rfl⟩).trans (le_max_right _ _)

def reciprocalJetBound (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (order : ℕ) : ℝ :=
  (exists_reciprocalJet_bound lower positive bounded order).choose

theorem reciprocalJetBound_one_le (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (order : ℕ) :
    1 ≤ reciprocalJetBound lower positive bounded order :=
  (exists_reciprocalJet_bound lower positive bounded order).choose_spec.1

theorem reciprocalJet_bound (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (order index : ℕ) (upper : index ≤ order) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    (order.choose index : ℝ) * ‖iteratedDerivWithin index (fun radius : ℝ => radius⁻¹) (Icc lower 1) radius‖ ≤
      reciprocalJetBound lower positive bounded order ∧
    (order.choose index : ℝ) * ‖iteratedDerivWithin index (fun radius : ℝ => radius⁻¹ ^ 2) (Icc lower 1) radius‖ ≤
      reciprocalJetBound lower positive bounded order := by
  have summand := Finset.single_le_sum (s := Finset.range (order + 1))
    (f := fun index => (order.choose index : ℝ) *
      (‖iteratedDerivWithin index (fun radius : ℝ => radius⁻¹) (Icc lower 1) radius‖ +
        ‖iteratedDerivWithin index (fun radius : ℝ => radius⁻¹ ^ 2) (Icc lower 1) radius‖))
    (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _)))
    (Finset.mem_range.mpr (by omega : index < order + 1))
  have total := summand.trans ((exists_reciprocalJet_bound lower positive bounded order).choose_spec.2 radius inside)
  rw [mul_add] at total
  constructor
  · exact (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))).trans total
  · exact (le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))).trans total

private theorem sum_norm_sq {E : Type*} [SeminormedAddCommGroup E] {ι : Type*}
    (indices : Finset ι) (values : ι → E) :
    ‖∑ index ∈ indices, values index‖ ^ 2 ≤ (indices.card : ℝ) * ∑ index ∈ indices, ‖values index‖ ^ 2 := by
  have cauchy := Finset.sum_mul_sq_le_sq_mul_sq indices (fun _ => (1 : ℝ)) (fun index => ‖values index‖)
  have bounded := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le indices values) 2
  exact bounded.trans (by simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using cauchy)

/-- The Leibniz row bound keeps every smaller genuine radial derivative. -/
theorem radialLeibniz_norm_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (order : ℕ) (coefficient : ℝ → ℝ) (value : ℝ → E) (domain : Set ℝ) (radius constant : ℝ)
    (coeffBound : ∀ index ≤ order,
      (order.choose index : ℝ) * ‖iteratedDerivWithin index coefficient domain radius‖ ≤ constant) :
    ‖radialLeibniz order coefficient value domain radius‖ ^ 2 ≤
      ((order + 1 : ℕ) : ℝ) * constant ^ 2 *
        ∑ index ∈ Finset.range (order + 1), ‖iteratedDerivWithin (order - index) value domain radius‖ ^ 2 := by
  have pointwise (index : ℕ) (member : index ∈ Finset.range (order + 1)) :
      ‖order.choose index • iteratedDerivWithin index coefficient domain radius •
        iteratedDerivWithin (order - index) value domain radius‖ ^ 2 ≤
        constant ^ 2 * ‖iteratedDerivWithin (order - index) value domain radius‖ ^ 2 := by
    have bound := mul_le_mul_of_nonneg_right (coeffBound index (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using member))
      (norm_nonneg (iteratedDerivWithin (order - index) value domain radius))
    have actual : ‖order.choose index • iteratedDerivWithin index coefficient domain radius •
        iteratedDerivWithin (order - index) value domain radius‖ ≤
        constant * ‖iteratedDerivWithin (order - index) value domain radius‖ := by
      simpa only [← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast, mul_assoc] using bound
    exact (pow_le_pow_left₀ (norm_nonneg _) actual 2).trans_eq (mul_pow _ _ _)
  have summed := Finset.sum_le_sum pointwise
  rw [← Finset.mul_sum] at summed
  have initial := sum_norm_sq (Finset.range (order + 1)) (fun index =>
    order.choose index • iteratedDerivWithin index coefficient domain radius •
      iteratedDerivWithin (order - index) value domain radius)
  exact initial.trans ((mul_le_mul_of_nonneg_left summed (Nat.cast_nonneg _)).trans_eq (by
    simp only [Finset.card_range, mul_assoc]))

end Grad.CircularHighRegularity
