import AJF2OriginalOmegaWeightedClosure

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularLowOrbit Grad.AnnularFluxTrace

/-- The original joint frequency needs only the pure angular and cell
generator of the requested order. -/
theorem highFrequency_power_bound (grade : ℕ) (mode : ℤ × ℤ) :
    |annularFrequency mode.1 mode.2 ^ grade| ≤ (4 : ℝ) ^ grade *
      (1 + |(mode.1 : ℝ)| ^ grade + |(mode.2 : ℝ)| ^ grade) := by
  have first := Grad.BoundaryTrace.two_term_pow_bound (1 + |(mode.1 : ℝ)|) |(mode.2 : ℝ)|
    (by positivity) (abs_nonneg _) grade
  have second := Grad.BoundaryTrace.two_term_pow_bound 1 |(mode.1 : ℝ)|
    zero_le_one (abs_nonneg _) grade
  simp only [one_pow] at second
  have powerOne : (1 : ℝ) ≤ 2 ^ grade := one_le_pow₀ (by norm_num)
  have square : (4 : ℝ) ^ grade = (2 : ℝ) ^ grade * (2 : ℝ) ^ grade := by
    rw [← mul_pow]
    norm_num
  rw [abs_of_nonneg (pow_nonneg (by unfold annularFrequency; positivity) grade), square]
  change ((1 + |(mode.1 : ℝ)|) + |(mode.2 : ℝ)|) ^ grade ≤ _
  apply first.trans
  have nonnegative : (0 : ℝ) ≤ 2 ^ grade := by positivity
  calc
    _ ≤ 2 ^ grade * (2 ^ grade * (1 + |(mode.1 : ℝ)| ^ grade) + |(mode.2 : ℝ)| ^ grade) :=
      mul_le_mul_of_nonneg_left (add_le_add second le_rfl) nonnegative
    _ ≤ 2 ^ grade * (2 ^ grade * (1 + |(mode.1 : ℝ)| ^ grade) + 2 ^ grade * |(mode.2 : ℝ)| ^ grade) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (le_mul_of_one_le_left (pow_nonneg (abs_nonneg (mode.2 : ℝ)) grade) powerOne)) nonnegative
    _ = _ := by ring

section Lp
variable {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem twoGenerator_pointwise (field angular cell : lp (fun _ : ι => V) 2)
    (angularFrequency cellFrequency : ι → ℤ) (grade : ℕ)
    (angularActual : ∀ index, angular index = (Complex.I * (angularFrequency index : ℂ)) ^ grade • field index)
    (cellActual : ∀ index, cell index = (Complex.I * (cellFrequency index : ℂ)) ^ grade • field index)
    (coefficient : ι → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bound : ∀ index, |coefficient index| ≤ constant *
      (1 + |(angularFrequency index : ℝ)| ^ grade + |(cellFrequency index : ℝ)| ^ grade)) (index : ι) :
    ‖(coefficient index : ℂ) • field index‖ ≤
      ‖constant • ((lpNormFamily field + lpNormFamily angular + lpNormFamily cell) index)‖ := by
  change ‖(coefficient index : ℂ) • field index‖ ≤
    ‖constant • (‖field index‖ + ‖angular index‖ + ‖cell index‖)‖
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, norm_smul, Real.norm_of_nonneg nonnegative,
    Real.norm_of_nonneg (by positivity), angularActual, cellActual,
    norm_smul, norm_smul, cellGeneratorFactor_norm, cellGeneratorFactor_norm]
  exact (mul_le_mul_of_nonneg_right (bound index) (norm_nonneg _)).trans_eq (by ring)

theorem twoGenerator_weighted_memℓp (field angular cell : lp (fun _ : ι => V) 2)
    (angularFrequency cellFrequency : ι → ℤ) (grade : ℕ)
    (angularActual : ∀ index, angular index = (Complex.I * (angularFrequency index : ℂ)) ^ grade • field index)
    (cellActual : ∀ index, cell index = (Complex.I * (cellFrequency index : ℂ)) ^ grade • field index)
    (coefficient : ι → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bound : ∀ index, |coefficient index| ≤ constant *
      (1 + |(angularFrequency index : ℝ)| ^ grade + |(cellFrequency index : ℝ)| ^ grade)) :
    Memℓp (fun index => (coefficient index : ℂ) • field index) 2 := by
  apply (lp.memℓp (constant • (lpNormFamily field + lpNormFamily angular + lpNormFamily cell))).mono'
  exact twoGenerator_pointwise field angular cell angularFrequency cellFrequency grade angularActual cellActual
    coefficient constant nonnegative bound

theorem twoGenerator_weighted_norm (field angular cell weighted : lp (fun _ : ι => V) 2)
    (angularFrequency cellFrequency : ι → ℤ) (grade : ℕ)
    (angularActual : ∀ index, angular index = (Complex.I * (angularFrequency index : ℂ)) ^ grade • field index)
    (cellActual : ∀ index, cell index = (Complex.I * (cellFrequency index : ℂ)) ^ grade • field index)
    (coefficient : ι → ℝ) (actual : ∀ index, weighted index = (coefficient index : ℂ) • field index)
    (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bound : ∀ index, |coefficient index| ≤ constant *
      (1 + |(angularFrequency index : ℝ)| ^ grade + |(cellFrequency index : ℝ)| ^ grade)) :
    ‖weighted‖ ≤ constant * (‖field‖ + ‖angular‖ + ‖cell‖) := by
  have pointwise : ‖weighted‖ ≤ ‖constant • (lpNormFamily field + lpNormFamily angular + lpNormFamily cell)‖ := by
    apply lp.norm_mono (by norm_num)
    intro index
    rw [actual]
    exact twoGenerator_pointwise field angular cell angularFrequency cellFrequency grade angularActual cellActual
      coefficient constant nonnegative bound index
  apply pointwise.trans
  rw [norm_smul, Real.norm_of_nonneg nonnegative]
  apply mul_le_mul_of_nonneg_left _ nonnegative
  have first := norm_add_le (lpNormFamily field + lpNormFamily angular) (lpNormFamily cell)
  have second := norm_add_le (lpNormFamily field) (lpNormFamily angular)
  have combined := first.trans (add_le_add second le_rfl)
  simpa only [lpNormFamily_norm] using combined

end Lp
end Grad.AnnularHighGenerators
