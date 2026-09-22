import LiteralFirstPair
import RadialDifferential
import CompactSmoothIntegral

noncomputable section

open Set
open scoped ContDiff

namespace Grad.NonlinearQuotient

open Grad.MainTarget Grad.PhysicalFamily Grad.Constraints

variable {Value : Type} [NormedAddCommGroup Value] [NormedSpace ℝ Value]

theorem cellSection_smooth {field : Plane → ℝ → Value} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ (Function.uncurry field) (Metric.ball 0 radius ×ˢ univ))
    (time : ℝ) : ContDiffOn ℝ ∞ (fun point => field point time) (Metric.ball 0 radius) := by
  exact smooth.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ membership =>
    ⟨membership, mem_univ _⟩)

theorem diskEuler_joint_smooth {field : Plane → ℝ → Value} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ (Function.uncurry field) (Metric.ball 0 radius ×ˢ univ)) :
    ContDiffOn ℝ ∞ (Function.uncurry (diskEuler field)) (Metric.ball 0 radius ×ˢ univ) := by
  have derivativeSmooth := integralParameterDerivative_smooth Metric.isOpen_ball smooth
  have productSmooth : ContDiffOn ℝ ∞ (fun argument : Plane × ℝ =>
      integralParameterDerivative (Function.uncurry field) argument argument.1)
      (Metric.ball 0 radius ×ˢ univ) := derivativeSmooth.clm_apply contDiffOn_fst
  apply productSmooth.congr
  intro argument membership
  have differentiable := (smooth.contDiffAt
    ((Metric.isOpen_ball.prod isOpen_univ).mem_nhds membership)).differentiableAt (by simp)
  exact (congrArg (fun derivative : Plane →L[ℝ] Value => derivative argument.1)
    (integralParameterDerivative_eq argument.1 argument.2 differentiable)).symm

theorem diskAngular_joint_smooth {field : Plane → ℝ → Value} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ (Function.uncurry field) (Metric.ball 0 radius ×ˢ univ)) :
    ContDiffOn ℝ ∞ (Function.uncurry (diskAngular field)) (Metric.ball 0 radius ×ˢ univ) := by
  have derivativeSmooth := integralParameterDerivative_smooth Metric.isOpen_ball smooth
  have turnSmooth : ContDiffOn ℝ ∞ (fun argument : Plane × ℝ => planeQuarterTurn argument.1)
      (Metric.ball 0 radius ×ˢ univ) := quarterTurnCLM.contDiff.comp_contDiffOn contDiffOn_fst
  have productSmooth : ContDiffOn ℝ ∞ (fun argument : Plane × ℝ =>
      integralParameterDerivative (Function.uncurry field) argument (planeQuarterTurn argument.1))
      (Metric.ball 0 radius ×ˢ univ) := derivativeSmooth.clm_apply turnSmooth
  apply productSmooth.congr
  intro argument membership
  have differentiable := (smooth.contDiffAt
    ((Metric.isOpen_ball.prod isOpen_univ).mem_nhds membership)).differentiableAt (by simp)
  exact (congrArg (fun derivative : Plane →L[ℝ] Value => derivative (planeQuarterTurn argument.1))
    (integralParameterDerivative_eq argument.1 argument.2 differentiable)).symm

theorem complexDot_contDiffOn
    {Source : Type} [NormedAddCommGroup Source] [NormedSpace ℝ Source]
    {domain : Set Source} {first second : Source → ComplexVec}
    (firstSmooth : ContDiffOn ℝ ∞ first domain) (secondSmooth : ContDiffOn ℝ ∞ second domain) :
    ContDiffOn ℝ ∞ (fun argument => complexDot (first argument) (second argument)) domain := by
  have firstCoordinate (coordinate : Fin 3) :
      ContDiffOn ℝ ∞ (fun argument => first argument coordinate) domain :=
    (PiLp.proj 2 (fun _ : Fin 3 => ℂ) coordinate : ComplexVec →L[ℝ] ℂ).contDiff.comp_contDiffOn firstSmooth
  have secondCoordinate (coordinate : Fin 3) :
      ContDiffOn ℝ ∞ (fun argument => second argument coordinate) domain :=
    (PiLp.proj 2 (fun _ : Fin 3 => ℂ) coordinate : ComplexVec →L[ℝ] ℂ).contDiff.comp_contDiffOn secondSmooth
  simpa only [complexDot, Fin.sum_univ_three] using
    (((firstCoordinate 0).mul (secondCoordinate 0)).add
      ((firstCoordinate 1).mul (secondCoordinate 1))).add
        ((firstCoordinate 2).mul (secondCoordinate 2))

theorem eulerAngularProduct_joint_smooth {field : Plane → ℝ → ComplexVec} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ (Function.uncurry field) (Metric.ball 0 radius ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun argument : Plane × ℝ =>
      complexDot (diskEuler field argument.1 argument.2) (diskAngular field argument.1 argument.2))
      (Metric.ball 0 radius ×ˢ univ) :=
  complexDot_contDiffOn (diskEuler_joint_smooth smooth) (diskAngular_joint_smooth smooth)

end Grad.NonlinearQuotient
