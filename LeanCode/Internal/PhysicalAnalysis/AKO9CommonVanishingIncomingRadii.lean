import AKO8GoodLogarithmicRadius

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace Grad.AnnularIncomingIntegrability

/-- The full common-radius selector: geometric decrease, explicit incoming
decay, convergence to the axis and avoidance of any prescribed null set. -/
theorem exists_common_vanishing_incoming_radii
    (upper : ℝ) (upperPositive : 0 < upper)
    (incoming : ℝ → ℝ) (measurable : Measurable incoming)
    (nonnegative : ∀ radius ∈ Ioc 0 upper, 0 ≤ incoming radius)
    (finite : (∫⁻ radius, ENNReal.ofReal (radius⁻¹ * incoming radius ^ 2)
      ∂volume.restrict (Ioc 0 upper)) < ⊤)
    (exceptional : Set ℝ) (null : volume exceptional = 0) :
    ∃ radii : ℕ → ℝ,
      (∀ index, radii index ∈ Ioc 0 upper) ∧
      (∀ index, radii index ∉ exceptional) ∧
      (∀ index, radii (index + 1) < radii index / 2) ∧
      StrictAnti radii ∧
      (∀ index, incoming (radii index) < 1 / ((index : ℝ) + 1)) ∧
      Tendsto radii atTop (𝓝 0) ∧
      Tendsto (incoming ∘ radii) atTop (𝓝 0) := by
  let State := {radius : ℝ // radius ∈ Ioc 0 upper}
  have initialExists := exists_good_logarithmic_radius upper upperPositive incoming measurable finite
    exceptional null (min upper 1) 1 (lt_min upperPositive (by norm_num)) (min_le_left _ _) (by norm_num)
  let first : State := ⟨Classical.choose initialExists,
    (Classical.choose_spec initialExists).1,
    (Classical.choose_spec initialExists).2.1.le.trans (min_le_left _ _)⟩
  have nextExists (index : ℕ) (previous : State) :=
    exists_good_logarithmic_radius upper upperPositive incoming measurable finite exceptional null
      (min (previous.val / 2) (1 / ((index : ℝ) + 2))) (1 / ((index : ℝ) + 2))
      (lt_min (half_pos previous.property.1) (by positivity))
      ((min_le_left _ _).trans ((half_le_self previous.property.1.le).trans previous.property.2)) (by positivity)
  let next : ℕ → State → State := fun index previous =>
    ⟨Classical.choose (nextExists index previous),
      (Classical.choose_spec (nextExists index previous)).1,
      (Classical.choose_spec (nextExists index previous)).2.1.le.trans
        ((min_le_left _ _).trans ((half_le_self previous.property.1.le).trans previous.property.2))⟩
  let sequence : ℕ → State := fun index => Nat.rec first (fun index previous => next index previous) index
  let radii : ℕ → ℝ := fun index => (sequence index).val
  have inside (index : ℕ) : radii index ∈ Ioc 0 upper := (sequence index).property
  have avoids (index : ℕ) : radii index ∉ exceptional := by
    cases index with
    | zero => exact (Classical.choose_spec initialExists).2.2.1
    | succ index => exact (Classical.choose_spec (nextExists index (sequence index))).2.2.1
  have geometric (index : ℕ) : radii (index + 1) < radii index / 2 :=
    (Classical.choose_spec (nextExists index (sequence index))).2.1.trans_le (min_le_left _ _)
  have radiusBound (index : ℕ) : radii index < 1 / ((index : ℝ) + 1) := by
    cases index with
    | zero => simpa only [radii,sequence,first,Nat.rec_zero,Nat.cast_zero,zero_add,div_one] using
        (Classical.choose_spec initialExists).2.1.trans_le (min_le_right _ _)
    | succ index => simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using
        (Classical.choose_spec (nextExists index (sequence index))).2.1.trans_le (min_le_right _ _)
  have incomingBound (index : ℕ) : incoming (radii index) < 1 / ((index : ℝ) + 1) := by
    cases index with
    | zero => simpa only [radii,sequence,first,Nat.rec_zero,Nat.cast_zero,zero_add,div_one] using (Classical.choose_spec initialExists).2.2.2
    | succ index => simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using
        (Classical.choose_spec (nextExists index (sequence index))).2.2.2
  have reciprocal : Tendsto (fun index : ℕ => 1 / ((index : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨radii,inside,avoids,geometric,?_,incomingBound,?_,?_⟩
  · apply strictAnti_nat_of_succ_lt
    intro index
    exact (geometric index).trans (half_lt_self (inside index).1)
  · exact squeeze_zero (fun index => (inside index).1.le) (fun index => (radiusBound index).le) reciprocal
  · exact squeeze_zero (fun index => nonnegative _ (inside index)) (fun index => (incomingBound index).le) reciprocal

end Grad.AnnularIncomingIntegrability
