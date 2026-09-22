import ANB10ScalarHomogeneity

noncomputable section
open scoped ENNReal
namespace Grad.BoundedScalarInverse

section HilbertColumns
variable {E : Type*} [NormedAddCommGroup E]

theorem lp_two_summable (field : lp (fun _ : ℤ × ℤ => E) 2) :
    Summable (fun output => ‖field output‖ ^ 2) := by
  have member := lp.memℓp field
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)] at member
  simpa using member

def hilbertColumn (field : lp (fun _ : ℤ × ℤ => E) 2) (cell : ℤ) : lp (fun _ : ℤ => E) 2 :=
  ⟨fun mode => field (mode, cell), by
    change Memℓp (fun mode : ℤ => field (mode, cell)) 2
    rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
    have summable := (lp_two_summable field).comp_injective (i := fun mode : ℤ => (mode, cell))
      (fun _ _ same => congrArg Prod.fst same)
    simpa [Function.comp_def] using summable⟩

theorem hilbertColumn_norm_sq (field : lp (fun _ : ℤ × ℤ => E) 2) (cell : ℤ) :
    ‖hilbertColumn field cell‖ ^ 2 = ∑' mode, ‖field (mode, cell)‖ ^ 2 := by
  have equality := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (hilbertColumn field cell)
  simpa [hilbertColumn] using equality

theorem hilbertColumns_summable (field : lp (fun _ : ℤ × ℤ => E) 2) :
    Summable (fun cell => ‖hilbertColumn field cell‖ ^ 2) := by
  have flipped : Summable (fun output : ℤ × ℤ => ‖field (output.2, output.1)‖ ^ 2) :=
    (Equiv.prodComm ℤ ℤ).summable_iff.mpr (lp_two_summable field)
  simpa only [hilbertColumn_norm_sq] using flipped.prod

def hilbertColumnSizes (field : lp (fun _ : ℤ × ℤ => E) 2) : lp (fun _ : ℤ => ℝ) 2 :=
  ⟨fun cell => ‖hilbertColumn field cell‖, by
    change Memℓp (fun cell : ℤ => ‖hilbertColumn field cell‖) 2
    rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
    simpa using hilbertColumns_summable field⟩

theorem hilbertColumnSizes_norm (field : lp (fun _ : ℤ × ℤ => E) 2) :
    ‖hilbertColumnSizes field‖ = ‖field‖ := by
  have outer := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (hilbertColumnSizes field)
  have total := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at outer total
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  calc
    _ = ∑' cell, ‖hilbertColumn field cell‖ ^ 2 := by simpa [hilbertColumnSizes] using outer
    _ = ∑' cell, ∑' mode, ‖field (mode, cell)‖ ^ 2 := by simp only [hilbertColumn_norm_sq]
    _ = ∑' output : ℤ × ℤ, ‖field (output.2, output.1)‖ ^ 2 :=
      ((Equiv.prodComm ℤ ℤ).summable_iff.mpr (lp_two_summable field)).tsum_prod.symm
    _ = ∑' output : ℤ × ℤ, ‖field output‖ ^ 2 := (Equiv.prodComm ℤ ℤ).tsum_eq (fun output => ‖field output‖ ^ 2)
    _ = _ := total.symm

def hilbertZeroCell (field : lp (fun _ : ℤ => E) 2) : lp (fun _ : ℤ × ℤ => E) 2 :=
  ⟨fun output => if output.2 = 0 then field output.1 else 0, by
    change Memℓp (fun output : ℤ × ℤ => if output.2 = 0 then field output.1 else 0) 2
    rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).2
    constructor
    · intro mode
      exact summable_of_ne_finset_zero (s := {0}) (by intro cell missing; simp_all)
    · have member := lp.memℓp field
      rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)] at member
      simpa [apply_ite] using member⟩

theorem hilbertZeroCell_norm (field : lp (fun _ : ℤ => E) 2) : ‖hilbertZeroCell field‖ = ‖field‖ := by
  have outer := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (hilbertZeroCell field)
  have inner := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at outer inner
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [outer, (lp_two_summable (hilbertZeroCell field)).tsum_prod]
  simpa [hilbertZeroCell, apply_ite] using inner.symm

end HilbertColumns
end Grad.BoundedScalarInverse
