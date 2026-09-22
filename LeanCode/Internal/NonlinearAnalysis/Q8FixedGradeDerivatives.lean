import Q8FixedGradeBounds
import N3AllOrders

noncomputable section

open scoped BigOperators ContDiff

namespace Grad.Q8FixedGrade

open Grad.CartesianState Grad.NonlinearQuotientBounds Grad.CoefficientMajorants

theorem placedFactor_hit {E : Type*} {order p : ℕ} (placement : Fin order ↪ Fin p)
    (base : E) (directions : Fin order → E) (index : Fin order) :
    multilinearPlacedFactor placement base directions (placement index) = directions index := by
  unfold multilinearPlacedFactor
  have hit : ∃ other, placement other = placement index := ⟨index, rfl⟩
  rw [dif_pos hit]
  exact congrArg directions (placement.injective (Classical.choose_spec hit))

theorem placedFactor_miss {E : Type*} {order p : ℕ} (placement : Fin order ↪ Fin p)
    (base : E) (directions : Fin order → E) (slot : Fin p)
    (miss : slot ∉ Finset.univ.map placement) :
    multilinearPlacedFactor placement base directions slot = base := by
  unfold multilinearPlacedFactor
  rw [dif_neg]
  rintro ⟨index, hit⟩
  exact miss (Finset.mem_map.mpr ⟨index, Finset.mem_univ _, hit⟩)

theorem prod_placedFactor {E : Type*} [CommMonoid E] {order p : ℕ}
    (placement : Fin order ↪ Fin p) (base : E) (directions : Fin order → E) :
    ∏ slot, multilinearPlacedFactor placement base directions slot =
      base ^ (p - order) * ∏ index, directions index := by
  classical
  rw [← Finset.prod_mul_prod_compl (Finset.univ.map placement)]
  have first : ∏ slot ∈ Finset.univ.map placement,
      multilinearPlacedFactor placement base directions slot = ∏ index, directions index := by
    rw [Finset.prod_map]
    exact Finset.prod_congr rfl (fun index _ => placedFactor_hit placement base directions index)
  have second : ∏ slot ∈ (Finset.univ.map placement)ᶜ,
      multilinearPlacedFactor placement base directions slot = base ^ (p - order) := by
    rw [Finset.prod_congr rfl (fun slot membership =>
      placedFactor_miss placement base directions slot (Finset.mem_compl.mp membership))]
    rw [Finset.prod_const, Finset.card_compl, Finset.card_map,
      Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
  rw [first, second, mul_comm]

theorem iteratedFDeriv_pow_apply (parameters : PhaseParameters) (grade order p : ℕ)
    (base : Carrier parameters grade) (directions : Fin order → Carrier parameters grade) :
    (iteratedFDeriv ℂ order (fun x : Carrier parameters grade => x ^ p) base) directions =
      (p.descFactorial order : ℂ) • (base ^ (p - order) * ∏ index, directions index) := by
  classical
  have diagonal : (fun x : Carrier parameters grade => x ^ p) =
      fun x => ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin p) (Carrier parameters grade)
        (fun _ => x) := by
    funext x
    simp [ContinuousMultilinearMap.mkPiAlgebra_apply]
  rw [diagonal, ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal_all_orders]
  simp_rw [ContinuousMultilinearMap.mkPiAlgebra_apply, prod_placedFactor]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_embedding_eq,
    Fintype.card_fin, Fintype.card_fin]
  rw [Nat.cast_smul_eq_nsmul]

theorem coefficientTerm_contDiff (parameters : PhaseParameters) (grade p : ℕ) :
    ContDiff ℂ ∞ (coefficientTerm (parameters := parameters) (grade := grade) p) :=
  (contDiff_id.pow p).const_smul (rootCoefficient p : ℂ)

theorem iteratedFDeriv_coefficientTerm_complex (parameters : PhaseParameters) (grade order p : ℕ)
    (base : Carrier parameters grade) (directions : Fin order → Carrier parameters grade) :
    (iteratedFDeriv ℂ order (coefficientTerm p) base) directions =
      derivativeTerm order p base directions := by
  have smooth : ContDiffAt ℂ order (fun x : Carrier parameters grade => x ^ p) base :=
    (contDiff_id.pow p).contDiffAt
  unfold coefficientTerm
  rw [iteratedFDeriv_const_smul_apply' smooth, smul_apply, iteratedFDeriv_pow_apply]
  simp [derivativeTerm, smul_smul]

theorem iteratedFDeriv_coefficientTerm_real (parameters : PhaseParameters) (grade order p : ℕ)
    (base : Carrier parameters grade) (directions : Fin order → Carrier parameters grade) :
    (iteratedFDeriv ℝ order (coefficientTerm p) base) directions =
      derivativeTerm order p base directions := by
  have restricted : iteratedFDeriv ℝ order (coefficientTerm p) base =
      (iteratedFDeriv ℂ order (coefficientTerm p) base).restrictScalars ℝ := by
    symm
    simpa only [Function.comp_apply] using
      ((coefficientTerm_contDiff parameters grade p).contDiffAt.of_le
        (show (order : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).restrictScalars_iteratedFDeriv
          (𝕜 := ℝ)
  rw [restricted]
  exact iteratedFDeriv_coefficientTerm_complex parameters grade order p base directions

end Grad.Q8FixedGrade
