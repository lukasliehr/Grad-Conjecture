import ANL5LiteralNormalKernel

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Grad.CircularNormalLift
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.BoundaryLift
open Grad.Constraints Grad.CircularHighWeak Grad.NonlinearRange

/-- Radial differentiation at the actual unit-circle endpoint, with outward sign. -/
theorem normalKernel_radial_hasDerivAt (mode : ℤ) (angle : CellCircle) :
    HasDerivAt (fun radius : ℝ => normalKernel mode (radius • boundaryCirclePoint angle))
      (fourier mode angle) 1 := by
  let dirichlet : ℝ → ℂ := fun radius => boundaryKernel (mode, 0) (radius • boundaryCirclePoint angle)
  have smooth : ContDiff ℝ ∞ dirichlet :=
    (boundaryKernel_smooth (mode, 0)).comp (contDiff_id.smul contDiff_const)
  have realFactor : HasDerivAt (fun radius : ℝ => ((radius - 1 : ℝ) : ℂ)) 1 1 := by
    simpa only [Function.comp_def, id_eq, Complex.ofRealCLM_apply, Complex.ofReal_one] using!
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 1 ((hasDerivAt_id (1 : ℝ)).sub_const 1)
  have derivative := realFactor.mul (smooth.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have value : dirichlet 1 = fourier mode angle := by
    simp only [dirichlet, one_smul, boundaryKernel_boundary]
  have calculated : HasDerivAt (fun radius : ℝ => ((radius - 1 : ℝ) : ℂ) * dirichlet radius)
      (fourier mode angle) 1 := by
    simpa only [Pi.mul_apply, sub_self, Complex.ofReal_zero, one_mul, zero_mul, add_zero, value] using! derivative
  apply calculated.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with radius positive
  rw [normalKernel, norm_smul, boundaryCirclePoint_norm, mul_one, Real.norm_of_nonneg positive.le]

theorem finiteNormalField_radial_hasDerivAt (modes : Finset ℤ)
    (values : ℤ → ComplexEuclidean 1) (angle : CellCircle) :
    HasDerivAt (fun radius : ℝ => finiteNormalField modes values (radius • boundaryCirclePoint angle))
      (∑ mode ∈ modes, fourier mode angle • values mode) 1 := by
  apply HasDerivAt.fun_sum
  intro mode _
  exact (normalKernel_radial_hasDerivAt mode angle).smul_const (values mode)

/-- Euler differentiation equals outward normal differentiation on |x|=1. -/
theorem finiteNormalJet_normal_boundary (modes : Finset ℤ) (values : ℤ → ComplexEuclidean 1)
    (angle : CellCircle) :
    (eulerJet (finiteNormalJet modes values)).value (boundaryDiskPoint angle) =
      ∑ mode ∈ modes, fourier mode angle • values mode := by
  rw [finiteNormalJet, eulerJet_global_value]
  have radial := (((finiteNormalField_smooth modes values).differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp_hasDerivAt
    1 ((hasDerivAt_id (1 : ℝ)).smul_const (boundaryCirclePoint angle))
  have agreement := radial.unique (finiteNormalField_radial_hasDerivAt modes values angle)
  simpa only [boundaryDiskPoint, id_eq, one_smul] using! agreement

theorem finiteNormalJet_normal_coefficient (modes : Finset ℤ) (values : ℤ → ComplexEuclidean 1)
    (frequency : ℤ) :
    fourierCoeff (fun angle : CellCircle =>
      (eulerJet (finiteNormalJet modes values)).value (boundaryDiskPoint angle)) frequency =
      if frequency ∈ modes then values frequency else 0 := by
  simp_rw [finiteNormalJet_normal_boundary]
  exact finiteFourier_coefficient modes values frequency

end Grad.CircularNormalLift
