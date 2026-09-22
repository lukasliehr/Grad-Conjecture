import SD1Interface

noncomputable section

open Grad.PDEBootstrap
open scoped ContDiff Topology

namespace Grad.SmoothDensity

theorem radial_radii (innerRadius outerRadius : ℝ) (nonnegative : 0 ≤ innerRadius)
    (strict : innerRadius < outerRadius) :
    innerRadius < plateauRadius innerRadius outerRadius ∧
      plateauRadius innerRadius outerRadius < supportRadius innerRadius outerRadius ∧
      supportRadius innerRadius outerRadius < outerRadius ∧
      0 < supportRadius innerRadius outerRadius ^ 2 - plateauRadius innerRadius outerRadius ^ 2 := by
  dsimp [plateauRadius, supportRadius]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  nlinarith [sq_nonneg (outerRadius - innerRadius)]

theorem radial_smooth (innerRadius outerRadius : ℝ) : ContDiff ℝ ∞ (radialFunction innerRadius outerRadius) :=
  Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub (contDiff_norm_sq ℝ)).div_const _)

theorem radial_one (innerRadius outerRadius : ℝ) (nonnegative : 0 ≤ innerRadius)
    (strict : innerRadius < outerRadius) :
    Set.EqOn (radialFunction innerRadius outerRadius) (fun _ => 1)
      (Metric.closedBall (0 : Spatial) (plateauRadius innerRadius outerRadius)) := by
  intro point membership
  have radii := radial_radii innerRadius outerRadius nonnegative strict
  have bound : ‖point‖ ≤ plateauRadius innerRadius outerRadius := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using membership
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ radii.2.2.2).mpr
  nlinarith [norm_nonneg point]

theorem radial_support (innerRadius outerRadius : ℝ) (nonnegative : 0 ≤ innerRadius)
    (strict : innerRadius < outerRadius) :
    tsupport (radialFunction innerRadius outerRadius) ⊆
      Metric.closedBall (0 : Spatial) (supportRadius innerRadius outerRadius) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro point membership
  by_contra outside
  have radii := radial_radii innerRadius outerRadius nonnegative strict
  have normBound : supportRadius innerRadius outerRadius < ‖point‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using outside
  have zero : radialFunction innerRadius outerRadius point = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    apply div_nonpos_of_nonpos_of_nonneg _ radii.2.2.2.le
    nlinarith [norm_nonneg point]
  exact membership zero

def radialCutoff (innerRadius outerRadius : ℝ) (nonnegative : 0 ≤ innerRadius)
    (strict : innerRadius < outerRadius) :
    Grad.CompactCutoff.Cutoff (Metric.closedBall (0 : Spatial) innerRadius)
      (Grad.SpatialDilation.disk outerRadius) where
  toFun := radialFunction innerRadius outerRadius
  smooth := radial_smooth innerRadius outerRadius
  compact := (isCompact_closedBall (0 : Spatial) (supportRadius innerRadius outerRadius)).of_isClosed_subset
    isClosed_closure (radial_support innerRadius outerRadius nonnegative strict)
  nonnegative _point := Real.smoothTransition.nonneg _
  atMostOne _point := Real.smoothTransition.le_one _
  supported := (radial_support innerRadius outerRadius nonnegative strict).trans
    (Metric.closedBall_subset_ball (radial_radii innerRadius outerRadius nonnegative strict).2.2.1)
  near := ⟨Metric.ball (0 : Spatial) (plateauRadius innerRadius outerRadius), Metric.isOpen_ball,
    Metric.closedBall_subset_ball (radial_radii innerRadius outerRadius nonnegative strict).1,
    Metric.ball_subset_ball ((radial_radii innerRadius outerRadius nonnegative strict).2.1.trans
      (radial_radii innerRadius outerRadius nonnegative strict).2.2.1).le,
    (radial_one innerRadius outerRadius nonnegative strict).mono Metric.ball_subset_closedBall⟩

theorem radialCutoff_laws (innerRadius outerRadius : ℝ) (nonnegative : 0 ≤ innerRadius)
    (strict : innerRadius < outerRadius) :
    RadialLaws innerRadius outerRadius (radialCutoff innerRadius outerRadius nonnegative strict) := by
  refine ⟨rfl, radial_one innerRadius outerRadius nonnegative strict,
    radial_support innerRadius outerRadius nonnegative strict,
    (radialCutoff innerRadius outerRadius nonnegative strict).germ, ?_, ?_⟩
  · intro isometry point
    change Real.smoothTransition _ = Real.smoothTransition _
    rw [isometry.norm_map]
  · exact Grad.CompactCutoff.orderedDerivative_bound _

theorem radial_goal : RadialGoal :=
  fun innerRadius outerRadius nonnegative strict =>
    ⟨radialCutoff innerRadius outerRadius nonnegative strict,
      radialCutoff_laws innerRadius outerRadius nonnegative strict⟩

end Grad.SmoothDensity
