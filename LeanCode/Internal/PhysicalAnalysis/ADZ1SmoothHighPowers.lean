import ADW6LiteralOmegaDenseConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularHighTilt

/-- The fixed BF radial exponent. -/
def highTiltExponent : ℝ := 9 / 4

theorem highTiltExponent_pos : 0 < highTiltExponent := by norm_num [highTiltExponent]

/-- A globally positive smooth radius which is literally `r` on a neighborhood
of `[lower,1]`.  This lets the closed smooth cores carry fractional powers
without changing any physical collar value. -/
def highSmoothRadius (lower : ℝ) (radius : ℝ) : ℝ :=
  let transition := Real.smoothTransition (2 - 4 * radius / lower)
  (1 - transition) * radius + transition * (lower / 4)

theorem highSmoothRadius_smooth (lower : ℝ) :
    ContDiff ℝ ∞ (highSmoothRadius lower) := by
  unfold highSmoothRadius
  fun_prop

theorem highSmoothRadius_eq (lower : ℝ) (positive : 0 < lower) (radius : ℝ)
    (above : lower / 2 ≤ radius) : highSmoothRadius lower radius = radius := by
  unfold highSmoothRadius
  rw [Real.smoothTransition.zero_of_nonpos]
  · ring
  · apply (sub_nonpos.mpr)
    apply (le_div_iff₀ positive).2
    nlinarith

theorem highSmoothRadius_pos (lower : ℝ) (positive : 0 < lower) (radius : ℝ) :
    0 < highSmoothRadius lower radius := by
  unfold highSmoothRadius
  let transition := Real.smoothTransition (2 - 4 * radius / lower)
  change 0 < (1 - transition) * radius + transition * (lower / 4)
  by_cases below : radius ≤ lower / 4
  · have one : transition = 1 := by
      apply Real.smoothTransition.one_of_one_le
      have quotient : 4 * radius / lower ≤ 1 := by
        apply (div_le_one positive).2
        nlinarith
      linarith
    rw [one]
    norm_num
    linarith
  · have radiusAbove : lower / 4 < radius := lt_of_not_ge below
    have radiusPositive : 0 < radius := by linarith
    have transitionNonnegative : 0 ≤ transition := Real.smoothTransition.nonneg _
    have transitionAtMostOne : transition ≤ 1 := Real.smoothTransition.le_one _
    calc
      (1 - transition) * radius + transition * (lower / 4) ≥
          (1 - transition) * (lower / 4) + transition * (lower / 4) := by
            have weighted :=
              mul_le_mul_of_nonneg_left radiusAbove.le (sub_nonneg.mpr transitionAtMostOne)
            linarith
      _ = lower / 4 := by ring
      _ > 0 := by linarith

/-- Global smooth realization of the physical multiplier `r^power`. -/
def highPowerCurve (lower power : ℝ) (positive : 0 < lower) : C(ℝ, ℝ) :=
  ⟨fun radius => highSmoothRadius lower radius ^ power,
    ((highSmoothRadius_smooth lower).continuous.rpow_const
      (fun radius => Or.inl (highSmoothRadius_pos lower positive radius).ne'))⟩

theorem highPowerCurve_smooth (lower power : ℝ) (positive : 0 < lower) :
    ContDiff ℝ ∞ (highPowerCurve lower power positive) := by
  change ContDiff ℝ ∞ (fun radius => highSmoothRadius lower radius ^ power)
  exact (highSmoothRadius_smooth lower).rpow_const_of_ne
    (fun radius => (highSmoothRadius_pos lower positive radius).ne')

/-- The exact global derivative paired with the smooth power. -/
def highPowerSlopeCurve (lower power : ℝ) (positive : 0 < lower) : C(ℝ, ℝ) :=
  ⟨fun radius => deriv (highPowerCurve lower power positive) radius,
    (contDiff_infty_iff_deriv.mp (highPowerCurve_smooth lower power positive)).2.continuous⟩

theorem highPowerCurve_hasDerivAt (lower power : ℝ) (positive : 0 < lower) (radius : ℝ) :
    HasDerivAt (highPowerCurve lower power positive)
      (highPowerSlopeCurve lower power positive radius) radius :=
  (highPowerCurve_smooth lower power positive).differentiable (by simp) radius |>.hasDerivAt

theorem highPowerCurve_physical (lower power : ℝ) (positive : 0 < lower)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    highPowerCurve lower power positive radius = radius ^ power := by
  change highSmoothRadius lower radius ^ power = radius ^ power
  rw [highSmoothRadius_eq lower positive radius]
  linarith [inside.1]

theorem highPowerSlopeCurve_physical (lower power : ℝ) (positive : 0 < lower)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    highPowerSlopeCurve lower power positive radius = power * radius ^ (power - 1) := by
  change deriv (highPowerCurve lower power positive) radius = _
  have half : lower / 2 < radius := by linarith [inside.1]
  have localEq : highPowerCurve lower power positive =ᶠ[nhds radius] (fun point => point ^ power) := by
    filter_upwards [Ioi_mem_nhds half] with point pointAbove
    change highSmoothRadius lower point ^ power = point ^ power
    rw [highSmoothRadius_eq lower positive point pointAbove.le]
  rw [localEq.deriv_eq]
  exact (Real.hasDerivAt_rpow_const (Or.inl (positive.trans_le inside.1).ne')).deriv

theorem highPowerCurve_inverse (lower power : ℝ) (positive : 0 < lower) (radius : ℝ) :
    highPowerCurve lower (-power) positive radius * highPowerCurve lower power positive radius = 1 := by
  change highSmoothRadius lower radius ^ (-power) * highSmoothRadius lower radius ^ power = 1
  rw [← Real.rpow_add (highSmoothRadius_pos lower positive radius), neg_add_cancel, Real.rpow_zero]

theorem highPowerSlopeCurve_cancel (lower power : ℝ) (positive : 0 < lower) (radius : ℝ) :
    highPowerSlopeCurve lower (-power) positive radius * highPowerCurve lower power positive radius +
      highPowerCurve lower (-power) positive radius * highPowerSlopeCurve lower power positive radius = 0 := by
  have product := (highPowerCurve_hasDerivAt lower (-power) positive radius).mul
    (highPowerCurve_hasDerivAt lower power positive radius)
  have constant : HasDerivAt
      (fun point => highPowerCurve lower (-power) positive point * highPowerCurve lower power positive point)
      0 radius := by
    apply (hasDerivAt_const radius (1 : ℝ)).congr_of_eventuallyEq
    filter_upwards [] with point
    exact highPowerCurve_inverse lower power positive point
  exact product.unique constant

theorem highPositivePower_bound (lower : ℝ) (positive : 0 < lower) (_bounded : lower ≤ 1)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |highPowerCurve lower highTiltExponent positive radius| ≤ 1 := by
  rw [highPowerCurve_physical lower highTiltExponent positive radius inside,
    abs_of_pos (Real.rpow_pos_of_pos (positive.trans_le inside.1) _)]
  simpa only [Real.one_rpow] using
    Real.rpow_le_rpow (positive.trans_le inside.1).le inside.2 highTiltExponent_pos.le

theorem highNegativePower_bound (lower : ℝ) (positive : 0 < lower) (_bounded : lower ≤ 1)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |highPowerCurve lower (-highTiltExponent) positive radius| ≤ lower ^ (-highTiltExponent) := by
  rw [highPowerCurve_physical lower (-highTiltExponent) positive radius inside,
    abs_of_pos (Real.rpow_pos_of_pos (positive.trans_le inside.1) _)]
  exact Real.rpow_le_rpow_of_nonpos positive inside.1 (neg_nonpos.mpr highTiltExponent_pos.le)

theorem highPower_outer (lower power : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) :
    highPowerCurve lower power positive 1 = 1 := by
  rw [highPowerCurve_physical lower power positive 1 ⟨bounded, le_rfl⟩, Real.one_rpow]

end Grad.AnnularHighTilt
