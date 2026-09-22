import ANB14WeightedScalarRowGain

noncomputable section
open scoped ENNReal
namespace Grad.BoundedScalarInverse

section HilbertSynthesis
variable {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]

def hilbertNorms (field : lp (fun _ : ℤ => E) 2) : lp (fun _ : ℤ => ℝ) 2 :=
  ⟨fun cell => ‖field cell‖, by
    change Memℓp (fun cell : ℤ => ‖field cell‖) 2
    have member := lp.memℓp field
    rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)] at member ⊢
    simpa using member⟩

theorem hilbertNorms_norm (field : lp (fun _ : ℤ => E) 2) : ‖hilbertNorms field‖ = ‖field‖ := by
  have first := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (hilbertNorms field)
  have second := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at first second
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact first.trans ((tsum_congr (fun cell => by simp [hilbertNorms])).trans second.symm)

def hilbertMajorant (bound : ℝ) (first : lp (fun _ : ℤ => E) 2) (second : lp (fun _ : ℤ => F) 2) :
    lp (fun _ : ℤ => ℝ) 2 := bound • (hilbertNorms first + hilbertNorms second)

theorem hilbertMajorant_apply (bound : ℝ) (first : lp (fun _ : ℤ => E) 2) (second : lp (fun _ : ℤ => F) 2) (cell : ℤ) :
    hilbertMajorant bound first second cell = bound * (‖first cell‖ + ‖second cell‖) := rfl

theorem hilbertMajorant_nonnegative (bound : ℝ) (nonnegative : 0 ≤ bound)
    (first : lp (fun _ : ℤ => E) 2) (second : lp (fun _ : ℤ => F) 2) (cell : ℤ) :
    0 ≤ hilbertMajorant bound first second cell := mul_nonneg nonnegative (add_nonneg (norm_nonneg _) (norm_nonneg _))

theorem hilbertMajorant_norm (bound : ℝ) (nonnegative : 0 ≤ bound)
    (first : lp (fun _ : ℤ => E) 2) (second : lp (fun _ : ℤ => F) 2) :
    ‖hilbertMajorant bound first second‖ ≤ bound * (‖first‖ + ‖second‖) := by
  unfold hilbertMajorant
  rw [norm_smul, Real.norm_of_nonneg nonnegative]
  exact (mul_le_mul_of_nonneg_left (norm_add_le _ _) nonnegative).trans_eq (by rw [hilbertNorms_norm, hilbertNorms_norm])

theorem hilbertSynthesis_mem (bound : ℝ) (nonnegative : 0 ≤ bound)
    (first : lp (fun _ : ℤ => E) 2) (second : lp (fun _ : ℤ => F) 2) (output : ℤ → G)
    (estimate : ∀ cell, ‖output cell‖ ≤ bound * (‖first cell‖ + ‖second cell‖)) : Memℓp output 2 := by
  apply (lp.memℓp (hilbertMajorant bound first second)).mono'
  intro cell
  exact (estimate cell).trans_eq (Real.norm_of_nonneg (hilbertMajorant_nonnegative bound nonnegative first second cell)).symm

theorem hilbertSynthesis_norm (bound : ℝ) (nonnegative : 0 ≤ bound)
    (first : lp (fun _ : ℤ => E) 2) (second : lp (fun _ : ℤ => F) 2) (output : lp (fun _ : ℤ => G) 2)
    (estimate : ∀ cell, ‖output cell‖ ≤ bound * (‖first cell‖ + ‖second cell‖)) :
    ‖output‖ ≤ bound * (‖first‖ + ‖second‖) := by
  have comparison : ‖output‖ ≤ ‖hilbertMajorant bound first second‖ := by
    apply lp.norm_mono (by norm_num)
    intro cell
    exact (estimate cell).trans_eq (Real.norm_of_nonneg (hilbertMajorant_nonnegative bound nonnegative first second cell)).symm
  exact comparison.trans (hilbertMajorant_norm bound nonnegative first second)

end HilbertSynthesis
end Grad.BoundedScalarInverse
