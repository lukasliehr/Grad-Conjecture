import ANR18PolarTestJets

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.BoundaryTrace
open Grad.NonlinearQuotient Grad.PhysicalFamily Grad.NonlinearDivision Grad.NonlinearQuotientBounds

private theorem modeSquare (mode : ℤ) :
    (Complex.I * (mode : ℂ)) ^ 2 = ((-(mode : ℝ) ^ 2 : ℝ) : ℂ) := by
  rw [mul_pow, Complex.I_sq, neg_one_mul]
  push_cast
  rfl

private theorem polarTestModel_angular_two (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (smooth : ContDiff ℝ ∞ test) (point : ℝ × ℝ) :
    angularJet 2 (polarTestModel mode vector test) point =
      (-(mode : ℝ) ^ 2 * test point.1) • (cellExponential mode point.2 • vector) := by
  rw [polarTestModel_angular 2 mode vector test smooth, modeSquare]
  change test point.1 • (cellExponential mode point.2 • (((-(mode : ℝ) ^ 2 : ℝ) : ℂ) • vector)) = _
  rw [Complex.coe_smul, smul_comm (cellExponential mode point.2) (-(mode : ℝ) ^ 2) vector, smul_smul]
  exact congrArg (fun scalar : ℝ => scalar • (cellExponential mode point.2 • vector)) (mul_comm _ _)

/-- The exact multiplied radial test Laplacian on every interior circle. -/
theorem radialTestLift_laplacian_multiplied (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (smooth : ContDiff ℝ ∞ test) (supported : tsupport test ⊆ Ioo (0 : ℝ) 1)
    (radius angle : ℝ) (inside : radius ∈ Ioo (0 : ℝ) 1) :
    radius ^ 2 • diskLaplacian (radialTestLift mode vector test) (polarPlane (radius, angle)) =
      (radius ^ 2 * deriv (deriv test) radius + radius * deriv test radius - (mode : ℝ) ^ 2 * test radius) •
        (cellExponential mode angle • vector) := by
  let field := radialTestLift mode vector test
  let model := polarTestModel mode vector test
  have agree : EqOn (field ∘ polarPlane) model polarOpenStrip := by
    intro point member
    exact radialTestLift_model mode vector test point.1 member.1 point.2
  have locally : field ∘ polarPlane =ᶠ[𝓝 (radius, angle)] model :=
    Filter.eventually_of_mem (polarOpenStrip_isOpen.mem_nhds inside) agree
  have first : radialField (field ∘ polarPlane) (radius, angle) = radialField model (radius, angle) :=
    congrArg (fun linear : (ℝ × ℝ) →L[ℝ] ComplexEuclidean 1 => linear (1, 0)) locally.fderiv_eq
  have second := radialIter_congr 2 (field ∘ polarPlane) model agree (show (radius, angle) ∈ polarOpenStrip from inside)
  have angular : angularJet 2 (field ∘ polarPlane) (radius, angle) = angularJet 2 model (radius, angle) :=
    congrArg (fun tensor : (ℝ × ℝ) [×2]→L[ℝ] ComplexEuclidean 1 => tensor (fun _ => (0, 1)))
      ((locally.iteratedFDeriv (𝕜 := ℝ) 2).eq_of_nhds)
  have laplacian := polar_laplacian_multiplied field (radialTestLift_smooth mode vector test smooth supported) radius angle
  rw [first, second, angular, polarTestModel_radial mode vector test smooth,
    polarTestModel_radial_two mode vector test smooth,
    polarTestModel_angular_two mode vector test smooth] at laplacian
  exact laplacian.trans (by
    dsimp only [polarTestModel, model]
    module)

/-- The closed-jet operator used by the actual weak equation is the literal
Cartesian Laplacian of the constructed compact test. -/
theorem laplacianJet_global_literal (field : SpatialPlane → ComplexEuclidean 1)
    (smooth : ContDiff ℝ ∞ field) (point : ClosedDisk) :
    (laplacianJet (globalClosedJet field smooth)).value point = diskLaplacian field point.val := by
  rw [laplacianJet_value]
  exact laplacianCoefficient_global field smooth point

end Grad.CircularHighRegularity
