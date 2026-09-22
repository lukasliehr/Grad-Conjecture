import NonlinearQuotientInterface

noncomputable section

open Set
open scoped ContDiff Topology

namespace Grad.NonlinearQuotient

open Grad.MainTarget Grad.PhysicalFamily Grad.GeometryClosure

def quarterTurnLinear : Plane →ₗ[ℝ] Plane where
  toFun := planeQuarterTurn
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;> simp [planeQuarterTurn, add_comm]
  map_smul' scalar point := by
    ext coordinate
    fin_cases coordinate <;> simp [planeQuarterTurn]

def quarterTurnCLM : Plane →L[ℝ] Plane := quarterTurnLinear.toContinuousLinearMap

@[simp] theorem quarterTurnCLM_apply (point : Plane) :
    quarterTurnCLM point = planeQuarterTurn point := rfl

theorem quarterTurn_twice (point : Plane) :
    planeQuarterTurn (planeQuarterTurn point) = -point := by
  ext coordinate
  fin_cases coordinate <;> simp [planeQuarterTurn]

theorem planeRotationAction_eq_cos_sin (angle : ℝ) (point : Plane) :
    planeRotationAction angle point =
      Real.cos angle • point + Real.sin angle • planeQuarterTurn point := by
  ext coordinate
  fin_cases coordinate
  · simp [planeRotationAction, planarRotation, Matrix.vecHead, Matrix.vecTail, planeQuarterTurn]
  · simp [planeRotationAction, planarRotation, Matrix.vecHead, Matrix.vecTail, planeQuarterTurn]
    ring

@[simp] theorem planeRotationAction_zero (point : Plane) :
    planeRotationAction 0 point = point := by
  simp [planeRotationAction_eq_cos_sin]

theorem planeRotationAction_hasDerivAt_zero (point : Plane) :
    HasDerivAt (fun angle => planeRotationAction angle point) (planeQuarterTurn point) 0 := by
  have derivative : HasDerivAt
      (fun angle => Real.cos angle • point + Real.sin angle • planeQuarterTurn point)
      ((-Real.sin 0) • point + Real.cos 0 • planeQuarterTurn point) 0 :=
    ((Real.hasDerivAt_cos (0 : ℝ)).smul_const point).add
      ((Real.hasDerivAt_sin (0 : ℝ)).smul_const (planeQuarterTurn point))
  simpa only [← planeRotationAction_eq_cos_sin, Real.sin_zero, neg_zero, zero_smul,
    Real.cos_zero, one_smul, zero_add] using derivative

theorem radial_fderiv_quarterTurn_zero
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (field : Plane → Target) (radius : ℝ)
    (radial : ∀ angle point, point ∈ Metric.ball (0 : Plane) radius →
      field (planeRotationAction angle point) = field point)
    (point : Plane) (pointIn : point ∈ Metric.ball (0 : Plane) radius)
    (differentiable : DifferentiableAt ℝ field point) :
    fderiv ℝ field point (planeQuarterTurn point) = 0 := by
  have outer : HasFDerivAt field (fderiv ℝ field point) (planeRotationAction 0 point) := by
    simpa using differentiable.hasFDerivAt
  have derivative := outer.comp_hasDerivAt 0
    (planeRotationAction_hasDerivAt_zero point)
  have constant : (fun angle => field (planeRotationAction angle point)) =
      fun _ => field point := funext (fun angle => radial angle point pointIn)
  change HasDerivAt (fun angle => field (planeRotationAction angle point)) _ 0 at derivative
  rw [constant] at derivative
  exact derivative.unique (hasDerivAt_const 0 (field point))

theorem radial_hessian_quarterTurn
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (field : Plane → Target) (radius : ℝ)
    (smooth : ContDiffOn ℝ ∞ field (Metric.ball (0 : Plane) radius))
    (radial : ∀ angle point, point ∈ Metric.ball (0 : Plane) radius →
      field (planeRotationAction angle point) = field point)
    (point : Plane) (pointIn : point ∈ Metric.ball (0 : Plane) radius) :
    fderiv ℝ (fderiv ℝ field) point (planeQuarterTurn point) (planeQuarterTurn point) =
      fderiv ℝ field point point := by
  have firstSmooth : ContDiffOn ℝ ∞ (fderiv ℝ field) (Metric.ball 0 radius) :=
    smooth.fderiv_of_isOpen Metric.isOpen_ball (by simp)
  have firstDifferentiable :=
    (firstSmooth.contDiffAt (Metric.isOpen_ball.mem_nhds pointIn)).differentiableAt (by simp)
  let curve : ℝ → Plane := fun scale => point + scale • planeQuarterTurn point
  have curveDerivative : HasDerivAt curve (planeQuarterTurn point) 0 := by
    have derivative : HasDerivAt
        (fun scale : ℝ => point + scale • planeQuarterTurn point)
        ((1 : ℝ) • planeQuarterTurn point) 0 :=
      (((hasDerivAt_id (0 : ℝ)).smul_const (planeQuarterTurn point)).const_add point)
    simpa only [one_smul] using derivative
  have curveZero : curve 0 = point := by simp [curve]
  have firstAt : HasFDerivAt (fderiv ℝ field) (fderiv ℝ (fderiv ℝ field) point) (curve 0) := by
    simpa only [curveZero] using firstDifferentiable.hasFDerivAt
  have derivativeFirst := firstAt.comp_hasDerivAt 0 curveDerivative
  have derivativeTurn := quarterTurnCLM.hasFDerivAt.comp_hasDerivAt 0 curveDerivative
  have derivative := derivativeFirst.clm_apply derivativeTurn
  simp only [quarterTurnCLM_apply, quarterTurn_twice, map_neg] at derivative
  have curveIn : ∀ᶠ scale in 𝓝 0, curve scale ∈ Metric.ball (0 : Plane) radius := by
    exact curveDerivative.continuousAt.eventually (Metric.isOpen_ball.mem_nhds (by simpa [curve] using pointIn))
  have eventuallyZero : (fun scale => fderiv ℝ field (curve scale) (quarterTurnCLM (curve scale)))
      =ᶠ[𝓝 0] fun _ => (0 : Target) := by
    filter_upwards [curveIn] with scale scaleIn
    exact radial_fderiv_quarterTurn_zero field radius radial (curve scale) scaleIn
      ((smooth.contDiffAt (Metric.isOpen_ball.mem_nhds scaleIn)).differentiableAt (by simp))
  have zeroDerivative := derivative.congr_of_eventuallyEq eventuallyZero.symm
  have equality := zeroDerivative.unique (hasDerivAt_const 0 (0 : Target))
  exact sub_eq_zero.mp (by simpa [curveZero, sub_eq_add_neg] using equality)

end Grad.NonlinearQuotient
