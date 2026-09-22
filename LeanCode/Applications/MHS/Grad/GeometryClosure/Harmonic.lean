import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! Elementary real-lift proofs for G22 and G23. No geometric or PDE assumptions. -/
noncomputable section
namespace Grad.GeometryClosure

/-- Membership in the additive subgroup πℤ, written with an explicit integer witness. -/
def InPiZ (x : ℝ) : Prop := ∃ k : ℤ, x = (k : ℝ) * Real.pi

/-- Membership in 2πℤ. -/
def InTwoPiZ (x : ℝ) : Prop := ∃ k : ℤ, x = (k : ℝ) * (2 * Real.pi)

/-- A real sign. -/
def IsSign (s : ℝ) : Prop := s = 1 ∨ s = -1

/-- The prescribed, unbundled two-harmonic seed angle. -/
def seedAngle (alpha0 delta lambda t : ℝ) : ℝ :=
  alpha0 + delta * (Real.cos t + lambda * Real.sin (2 * t))

theorem seedAngle_continuous (alpha0 delta lambda : ℝ) :
    Continuous (seedAngle alpha0 delta lambda) := by
  unfold seedAngle
  fun_prop

/-- G22, using the intermediate value theorem at an intervening half-integer. -/
theorem continuous_integer_valued_constant (f : ℝ → ℝ) (hf : Continuous f)
    (hi : ∀ t, ∃ k : ℤ, f t = (k : ℝ)) : ∃ k : ℤ, ∀ t, f t = (k : ℝ) := by
  have no_lt (a b : ℝ) : ¬ f a < f b := by
    intro hab
    obtain ⟨m, hm⟩ := hi a
    obtain ⟨n, hn⟩ := hi b
    have hmn : m < n := by exact_mod_cast (show (m : ℝ) < n by simpa [hm, hn] using hab)
    have hmn' : (m : ℝ) + 1 ≤ n := by exact_mod_cast (show m + 1 ≤ n by omega)
    obtain ⟨t, ht⟩ := intermediate_value_univ a b hf
      (show (m : ℝ) + 1 / 2 ∈ Set.Icc (f a) (f b) by rw [hm, hn]; constructor <;> linarith)
    obtain ⟨j, hj⟩ := hi t
    have hlow : m < j := by exact_mod_cast (show (m : ℝ) < j by linarith)
    have hupp : j < m + 1 := by exact_mod_cast (show (j : ℝ) < (m : ℝ) + 1 by linarith)
    omega
  obtain ⟨k, hk⟩ := hi 0
  refine ⟨k, fun t => ?_⟩
  have : f t = f 0 := le_antisymm (le_of_not_gt (no_lt 0 t)) (le_of_not_gt (no_lt t 0))
  exact this.trans hk

/-- G22, a pointwise congruence has one fixed integer lift on all of ℝ. -/
theorem continuous_pi_congruence_lift (f : ℝ → ℝ) (hf : Continuous f)
    (hi : ∀ t, InPiZ (f t)) : ∃ k : ℤ, ∀ t, f t = (k : ℝ) * Real.pi := by
  have hc : Continuous (fun t => f t / Real.pi) := hf.div_const _
  have hv : ∀ t, ∃ k : ℤ, f t / Real.pi = (k : ℝ) := by
    intro t
    obtain ⟨k, hk⟩ := hi t
    exact ⟨k, by rw [hk]; field_simp⟩
  obtain ⟨k, hk⟩ := continuous_integer_valued_constant _ hc hv
  exact ⟨k, fun t => (div_eq_iff Real.pi_ne_zero).mp (hk t)⟩

theorem cos_eq_one_iff_two_pi (c : ℝ) : Real.cos c = 1 ↔ InTwoPiZ c := by
  simpa [InTwoPiZ, eq_comm] using Real.cos_eq_one_iff c

/-- Simultaneous sine/cosine periodicity, also used in the tensor congruence. -/
theorem trig_add_two_pi {c : ℝ} (hc : InTwoPiZ c) (t : ℝ) :
    Real.cos (t + c) = Real.cos t ∧ Real.sin (t + c) = Real.sin t := by
  obtain ⟨k, rfl⟩ := hc
  exact ⟨Real.cos_add_int_mul_two_pi t k, Real.sin_add_int_mul_two_pi t k⟩

theorem two_pi_double {c : ℝ} (hc : InTwoPiZ c) : InTwoPiZ (2 * c) := by
  obtain ⟨k, hk⟩ := hc
  refine ⟨2 * k, ?_⟩
  push_cast
  rw [hk]
  ring

/-- First and second harmonic behavior under a half-period in the input. -/
theorem signed_half_period {sigma : ℝ} (hs : IsSign sigma) (t c : ℝ) :
    Real.cos (sigma * (t + Real.pi) + c) = -Real.cos (sigma * t + c) ∧
    Real.sin (2 * (sigma * (t + Real.pi) + c)) = Real.sin (2 * (sigma * t + c)) := by
  rcases hs with rfl | rfl
  · simp only [one_mul]
    constructor
    · rw [show t + Real.pi + c = (t + c) + Real.pi by ring, Real.cos_add_pi]
    · rw [show 2 * (t + Real.pi + c) = 2 * (t + c) + 2 * Real.pi by ring,
        Real.sin_add_two_pi]
  · simp only [neg_one_mul]
    constructor
    · rw [show -(t + Real.pi) + c = (-t + c) - Real.pi by ring, Real.cos_sub_pi]
    · rw [show 2 * (-(t + Real.pi) + c) = 2 * (-t + c) - 2 * Real.pi by ring,
        Real.sin_sub_two_pi]

/-- G23: the literal four-point sum, for either input sign and any phase. -/
theorem four_point_harmonic_sum (alpha0 delta mu c sigma : ℝ) (hs : IsSign sigma) :
    seedAngle alpha0 delta mu (sigma * 0 + c) +
    seedAngle alpha0 delta mu (sigma * (Real.pi / 2) + c) +
    seedAngle alpha0 delta mu (sigma * Real.pi + c) +
    seedAngle alpha0 delta mu (sigma * (3 * Real.pi / 2) + c) = 4 * alpha0 := by
  rcases hs with rfl | rfl <;>
    simp only [seedAngle, one_mul, neg_one_mul, mul_zero, zero_add, Real.sin_two_mul] <;>
    rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring] <;>
    simp only [neg_add, Real.cos_add, Real.sin_add, Real.cos_neg,
      Real.sin_neg, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two] <;> ring

/-- G23: the four-point sum eliminates the vertical sign and the fixed integer lift. -/
theorem harmonic_congruence_vertical_sign (alpha0 delta lambda mu sigma chi c : ℝ)
    (hs : IsSign sigma) (hx : IsSign chi) (ha : ¬ InPiZ (2 * alpha0))
    (h : ∀ t, InPiZ (seedAngle alpha0 delta mu (sigma * t + c) -
      chi * seedAngle alpha0 delta lambda t)) :
    chi = 1 ∧ ∀ t, seedAngle alpha0 delta mu (sigma * t + c) =
      seedAngle alpha0 delta lambda t := by
  have hc : Continuous (fun t => seedAngle alpha0 delta mu (sigma * t + c) -
      chi * seedAngle alpha0 delta lambda t) := by
    unfold seedAngle
    fun_prop
  obtain ⟨k, hk⟩ := continuous_pi_congruence_lift _ hc h
  have hs1 := four_point_harmonic_sum alpha0 delta mu c sigma hs
  have hs2 := four_point_harmonic_sum alpha0 delta lambda 0 1 (Or.inl rfl)
  simp only [one_mul, add_zero] at hs2
  have hsum : (1 - chi) * alpha0 = (k : ℝ) * Real.pi := by
    linear_combination (hk 0 + hk (Real.pi / 2) + hk Real.pi + hk (3 * Real.pi / 2) -
      hs1 + chi * hs2) / 4
  have hchi : chi = 1 := by
    rcases hx with hpos | hneg
    · exact hpos
    · exfalso
      apply ha
      exact ⟨k, by rw [hneg] at hsum; linarith⟩
  have hk0 : (k : ℝ) * Real.pi = 0 := by rw [hchi] at hsum; linarith
  refine ⟨hchi, fun t => ?_⟩
  have ht := hk t
  rw [hchi, one_mul, hk0] at ht
  linarith

/-- G23: subtraction at t+π isolates the first harmonic and fixes the phase. -/
theorem harmonic_first_period (alpha0 delta lambda mu sigma c : ℝ)
    (hd : delta ≠ 0) (hs : IsSign sigma)
    (h : ∀ t, seedAngle alpha0 delta mu (sigma * t + c) =
      seedAngle alpha0 delta lambda t) :
    (∀ t, Real.cos (sigma * t + c) = Real.cos t) ∧ InTwoPiZ c := by
  have hid (t : ℝ) : Real.cos (sigma * t + c) + mu * Real.sin (2 * (sigma * t + c)) =
      Real.cos t + lambda * Real.sin (2 * t) := by
    have ht := h t
    unfold seedAngle at ht
    exact mul_left_cancel₀ hd (add_left_cancel ht)
  have hcos (t : ℝ) : Real.cos (sigma * t + c) = Real.cos t := by
    have h1 := hid t
    have h2 := hid (t + Real.pi)
    obtain ⟨hc, hh⟩ := signed_half_period hs t c
    obtain ⟨hc', hh'⟩ := signed_half_period (Or.inl rfl : IsSign (1 : ℝ)) t 0
    simp only [one_mul, add_zero] at hc' hh'
    rw [hc, hh, hc', hh'] at h2
    linarith
  refine ⟨hcos, (cos_eq_one_iff_two_pi c).mp ?_⟩
  simpa using hcos 0

/-- G23: evaluate the second coefficient at π/4 after removing the phase. -/
theorem harmonic_second_coefficient (alpha0 delta lambda mu sigma c : ℝ)
    (hd : delta ≠ 0) (hs : IsSign sigma) (hc : InTwoPiZ c)
    (h : ∀ t, seedAngle alpha0 delta mu (sigma * t + c) =
      seedAngle alpha0 delta lambda t) : sigma * mu = lambda := by
  have ht := h (Real.pi / 4)
  unfold seedAngle at ht
  have he := mul_left_cancel₀ hd (add_left_cancel ht)
  rw [(trig_add_two_pi hc _).1] at he
  rw [show 2 * (sigma * (Real.pi / 4) + c) =
    2 * (sigma * (Real.pi / 4)) + 2 * c by ring,
    (trig_add_two_pi (two_pi_double hc) _).2] at he
  rcases hs with rfl | rfl
  · simp only [one_mul] at he ⊢
    rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two] at he
    linarith
  · simp only [neg_one_mul, Real.cos_neg] at he ⊢
    rw [show 2 * -(Real.pi / 4) = -(Real.pi / 2) by ring,
      show 2 * (Real.pi / 4) = Real.pi / 2 by ring,
      Real.sin_neg, Real.sin_pi_div_two] at he
    linarith

/-- Exact periodicity of the prescribed angle, with an arbitrary integer shift. -/
theorem seedAngle_periodic_shift (alpha0 delta lambda t c : ℝ) (hc : InTwoPiZ c) :
    seedAngle alpha0 delta lambda (t + c) = seedAngle alpha0 delta lambda t := by
  simp only [seedAngle, mul_add, (trig_add_two_pi hc t).1,
    (trig_add_two_pi (two_pi_double hc) (2 * t)).2]

/-- G23: complete two-parameter, two-sign rigidity, including the converse. -/
theorem two_harmonic_rigidity (alpha0 delta lambda mu sigma chi c : ℝ)
    (hl : 0 < lambda) (hm : 0 < mu) (hd : delta ≠ 0)
    (ha : ¬ InPiZ (2 * alpha0)) (hs : IsSign sigma) (hx : IsSign chi) :
    (∀ t, InPiZ (seedAngle alpha0 delta mu (sigma * t + c) -
      chi * seedAngle alpha0 delta lambda t)) ↔
      chi = 1 ∧ sigma = 1 ∧ InTwoPiZ c ∧ mu = lambda := by
  constructor
  · intro h
    obtain ⟨hchi, heq⟩ := harmonic_congruence_vertical_sign _ _ _ _ _ _ _ hs hx ha h
    obtain ⟨_, hc⟩ := harmonic_first_period _ _ _ _ _ _ hd hs heq
    have hcoef := harmonic_second_coefficient _ _ _ _ _ _ hd hs hc heq
    have hsigma : sigma = 1 := by
      rcases hs with hp | hn
      · exact hp
      · rw [hn] at hcoef; nlinarith
    refine ⟨hchi, hsigma, hc, ?_⟩
    simpa [hsigma] using hcoef
  · rintro ⟨rfl, rfl, hc, rfl⟩ t
    simp only [one_mul, seedAngle_periodic_shift _ _ _ _ _ hc, sub_self]
    exact ⟨0, by simp⟩

end Grad.GeometryClosure
