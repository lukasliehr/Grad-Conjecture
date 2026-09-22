import AIA3ActualHighEndpointCross
import AHX9ExactRetainedL2Consumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCircularForm
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularKernelL2

/-- Exact zero-shift kernel coefficient law, retaining the same weighted trace carrier. -/
theorem zeroShift_negativeTrace_coefficient {input output : ℕ} (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FullTwoFrequencyKernel parameters input output) (diagonal : ZeroShiftKernel kernel)
    (field : NegativeTrace parameters angular cell input) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell (fullNegativeKernelAction parameters angular cell kernel field) mode =
      kernel.entry (0, 0) mode (negativeTraceCoefficient parameters angular cell field mode) := by
  rw [← (fullNegativeKernelAction_coefficient_hasSum parameters angular cell kernel field mode).tsum_eq,
    tsum_eq_single (0, 0) (by
      intro shift nonzero
      rw [diagonal shift nonzero, zero_apply])]
  simp only [twoFrequencyTranslation_apply, sub_zero]

/-- Any finite vector is the literal coefficient of an actual complete negative trace. -/
theorem exists_negativeTrace_coefficient (parameters : PhaseParameters) (angular cell dimension : ℕ)
    (mode : ℤ × ℤ) (value : ComplexEuclidean dimension) :
    ∃ field : NegativeTrace parameters angular cell dimension,
      negativeTraceCoefficient parameters angular cell field mode = value := by
  refine ⟨lp.single 2 mode ((negativeTraceWeight parameters angular cell mode : ℂ) • value), ?_⟩
  have nonzero : (negativeTraceWeight parameters angular cell mode : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (negativeTraceWeight_pos parameters angular cell mode).ne'
  simp only [negativeTraceCoefficient, lp.single_apply, Pi.single_apply]
  exact inv_smul_smul₀ nonzero value

/-- Actual completed action for an arbitrary zero-shift kernel; no new multiplier norm is needed. -/
theorem completedBulkKernel_zeroShift_ae {input output : ℕ}
    (parameters : PhaseParameters) (power : ℕ) (lower : ℝ)
    (radius : ℝ → RadialPoint) (radiusContinuous : Continuous radius)
    (kernel : (x : ℝ) → RadialKernel parameters (radius x) input output)
    (measurable : ∀ shift mode, AEStronglyMeasurable (fun x => (kernel x).entry shift mode) (volume.restrict (Icc lower 1)))
    (bound : ℝ) (moment : ∀ᵐ x ∂volume.restrict (Icc lower 1),
      fullKernelMoment (radialKernelParameters parameters (radius x)) power (kernel x) ≤ bound)
    (diagonal : ∀ x, ZeroShiftKernel (kernel x)) (field : DivisionRow input lower) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1), ∀ mode,
      completedBulkKernel parameters power lower radius radiusContinuous kernel measurable bound moment field mode x =
        (kernel x).entry (0, 0) mode (field mode x) := by
  filter_upwards [completedBulkKernel_ae parameters power lower radius radiusContinuous kernel measurable bound moment field]
    with x actual
  intro mode
  rw [← (actual mode).tsum_eq, tsum_eq_single (0, 0) (by
    intro shift nonzero
    rw [diagonal x shift nonzero, zero_apply, smul_zero])]
  rw [bulkWeightRatio_zero]
  simp only [Complex.ofReal_one, one_smul, twoFrequencyTranslation_apply, sub_zero]

end Grad.AnnularCircularForm
