import AJH2FaithfulPolynomialObservation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularRadialSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.BoundaryLift

/-- Every finite Fourier field is an observation of an original strong trace. -/
theorem polynomialObservation_single (parameters : PhaseParameters) (power dimension : ℕ)
    (mode : ℤ × ℤ) (value : ComplexEuclidean dimension) :
    polynomialObservation parameters power dimension (lp.single 2 mode value) =
      lp.single 2 mode ((polynomialObservationFactor parameters power mode : ℂ) • value) := by
  apply lp.ext
  funext other
  change (polynomialObservationFactor parameters power other : ℂ) • (lp.single 2 mode value : CellL2 dimension) other = _
  by_cases same : other = mode
  · subst other; simp
  · simp [lp.single_apply, same]

/-- Dense range permits reuse of the accepted exact analytic kernel algebra
for the same operators in polynomial coordinates. -/
theorem polynomialObservation_denseRange (parameters : PhaseParameters) (power dimension : ℕ) :
    DenseRange (polynomialObservation parameters power dimension) := by
  intro field
  apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by norm_num) field)
  apply Eventually.of_forall
  intro indices
  apply subset_closure
  change (∑ mode ∈ indices, lp.single 2 mode (field mode)) ∈
    (polynomialObservation parameters power dimension).toLinearMap.range
  apply Submodule.sum_mem
  intro mode _
  refine ⟨lp.single 2 mode ((polynomialObservationFactor parameters power mode : ℂ)⁻¹ • field mode), ?_⟩
  change polynomialObservation parameters power dimension
    (lp.single 2 mode ((polynomialObservationFactor parameters power mode : ℂ)⁻¹ • field mode)) = lp.single 2 mode (field mode)
  rw [polynomialObservation_single, smul_inv_smul₀
    (Complex.ofReal_ne_zero.mpr (polynomialObservationFactor_positive parameters power mode).ne')]

/-- Literal intertwining with the already checked full negative-half action. -/
theorem polynomialObservation_kernel {source target : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (kernel : FullTwoFrequencyKernel parameters source target)
    (field : NegativeTrace parameters (power + 1) (power + 1) source) :
    polynomialObservation parameters power target
      (fullNegativeKernelAction parameters (power + 1) (power + 1) kernel field) =
      polynomialKernelAction parameters power kernel (polynomialObservation parameters power source field) := by
  apply lp.ext
  funext mode
  rw [polynomialObservation_apply]
  have original := fullNegativeKernelAction_coefficient_hasSum parameters (power + 1) (power + 1) kernel field mode
  have scaled := ((annularFrequency mode.1 mode.2 ^ power : ℂ) •
    ContinuousLinearMap.id ℂ (ComplexEuclidean target)).hasSum original
  have actual := polynomialKernelAction_coefficient parameters power kernel
    (polynomialObservation parameters power source field) mode
  apply scaled.unique
  apply actual.congr_fun
  intro shift
  rw [polynomialObservation_apply, map_smul, smul_smul]
  symm
  change ((polynomialWeightRatio power shift mode : ℂ) *
    (annularFrequency (twoFrequencyTranslation shift mode).1 (twoFrequencyTranslation shift mode).2 ^ power : ℂ)) •
    kernel.entry shift (twoFrequencyTranslation shift mode)
      (negativeTraceCoefficient parameters (power + 1) (power + 1) field (twoFrequencyTranslation shift mode)) =
    (annularFrequency mode.1 mode.2 ^ power : ℂ) •
    kernel.entry shift (twoFrequencyTranslation shift mode)
      (negativeTraceCoefficient parameters (power + 1) (power + 1) field (twoFrequencyTranslation shift mode))
  congr 1
  unfold polynomialWeightRatio
  push_cast
  exact div_mul_cancel₀ _ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (annularFrequency_pos (twoFrequencyTranslation shift mode)).ne'))

/-- SAME kernel composition; the accepted BKB action law is reused through
the dense observation, rather than rebuilding its convolution machinery. -/
theorem polynomialKernelAction_comp {source middle target : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (outer : FullTwoFrequencyKernel parameters middle target)
    (inner : FullTwoFrequencyKernel parameters source middle) :
    polynomialKernelAction parameters power (fullKernelComposition outer inner) =
      (polynomialKernelAction parameters power outer).comp (polynomialKernelAction parameters power inner) := by
  apply ContinuousLinearMap.ext
  have same := (polynomialObservation_denseRange parameters power source).equalizer
    (polynomialKernelAction parameters power (fullKernelComposition outer inner)).continuous
    ((polynomialKernelAction parameters power outer).comp (polynomialKernelAction parameters power inner)).continuous
  have equality := same (by
    funext field
    change polynomialKernelAction parameters power (fullKernelComposition outer inner)
      (polynomialObservation parameters power source field) = _
    rw [← polynomialObservation_kernel, fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
      polynomialObservation_kernel, polynomialObservation_kernel]
    rfl)
  exact fun field => congrFun equality field

end Grad.AnnularRadialSmoothness
