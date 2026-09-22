import RealLiteralRowsInterface
import LiteralRowsProof

noncomputable section

open Set
open scoped ContDiff

namespace Grad.NonlinearQuotient

open Grad.MainTarget Grad.PhysicalFamily Grad.Constraints

theorem complexAngularAverage_ofReal (field : Plane → ℝ → ℝ) (point : Plane) (time : ℝ) :
    complexAngularAverage (complexifyPotential field) point time = (angularAverage field point time : ℂ) := by
  have integralCast := Complex.ofRealLI.intervalIntegral_comp_comm
    (fun angle => field (planeRotationAction angle point) time) (a := 0) (b := 2 * Real.pi)
    (μ := MeasureTheory.volume)
  change (2 * Real.pi)⁻¹ • (∫ angle in (0 : ℝ)..2 * Real.pi,
      Complex.ofRealLI (field (planeRotationAction angle point) time)) = _
  rw [integralCast]
  simp [angularAverage, Complex.real_smul]

theorem complexAngularAverage_congr_on_ball {first second : Plane → ℝ → ℂ} {radius : ℝ}
    (equality : ∀ point ∈ Metric.ball (0 : Plane) radius, ∀ time, first point time = second point time)
    (point : Plane) (pointIn : point ∈ Metric.ball (0 : Plane) radius) (time : ℝ) :
    complexAngularAverage first point time = complexAngularAverage second point time := by
  unfold complexAngularAverage
  congr 1
  apply intervalIntegral.integral_congr
  intro angle _
  exact equality _ (by simpa [Metric.mem_ball, dist_zero_right] using pointIn) time

theorem complexRemoveAngularAverage_ofReal {complexField : Plane → ℝ → ℂ}
    {realField : Plane → ℝ → ℝ} {radius : ℝ}
    (equality : ∀ point ∈ Metric.ball (0 : Plane) radius, ∀ time,
      complexField point time = (realField point time : ℂ))
    (point : Plane) (pointIn : point ∈ Metric.ball (0 : Plane) radius) (time : ℝ) :
    complexRemoveAngularAverage complexField point time = (removeAngularAverage realField point time : ℂ) := by
  unfold complexRemoveAngularAverage removeAngularAverage
  rw [equality point pointIn time,
    complexAngularAverage_congr_on_ball (second := complexifyPotential realField) equality point pointIn time,
    complexAngularAverage_ofReal]
  exact (Complex.ofReal_sub _ _).symm

theorem timeSection_smooth {Value : Type} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {field : Plane → ℝ → Value} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ (Function.uncurry field) (Metric.ball 0 radius ×ˢ univ))
    {point : Plane} (pointIn : point ∈ Metric.ball (0 : Plane) radius) :
    ContDiff ℝ ∞ (field point) := by
  apply contDiffOn_univ.mp
  exact smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun _ _ => ⟨pointIn, mem_univ _⟩)

theorem complexAffineStateDerivative_complexify (cellLength epsilon : ℝ)
    (mapping : Plane → ℝ → Vec) (point : Plane) (time : ℝ)
    (differentiable : DifferentiableAt ℝ (mapping point) time) :
    complexAffineStateDerivative cellLength epsilon (complexifyMapping mapping) point time =
      complexifyVec (affineStateDerivative cellLength epsilon mapping point time) := by
  have direction : complexifyVecCLM tangentDirection = EuclideanSpace.single 1 1 := by
    ext coordinate
    simp [tangentDirection, basisVector, complexifyVec]
    split_ifs <;> simp
  unfold complexAffineStateDerivative affineStateDerivative complexifyMapping
  rw [cellDerivative_postcompose complexifyVecCLM mapping point time differentiable]
  change _ = complexifyVecCLM _
  rw [map_add, map_add, map_smul, map_smul, direction]
  simp only [complexifyVecCLM_apply, complexTangentGenerator_complexify]

end Grad.NonlinearQuotient
