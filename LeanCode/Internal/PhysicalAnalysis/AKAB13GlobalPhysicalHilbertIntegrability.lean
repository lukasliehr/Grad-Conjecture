import AKAB12PhysicalCoefficientOverRadius

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Grad.WeightedAxisRemoval
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceBoundaryTrace
open Grad.AnnularCurrentLow Grad.ActualPuncturedReconstruction Grad.PuncturedRetainedEnergy

variable {dimension : ℕ} (parameters : PhaseParameters) (collars : ℕ → ℝ)
    (positive : ∀ index, 0 < collars index) (decreasing : Antitone collars)
    (cofinal : Tendsto collars atTop (𝓝 0))
    (fields : ∀ index, DivisionRow dimension (collars index)) (curve : ℝ → CellL2 dimension)
    (same : ∀ index, ∀ᵐ radius ∂volume.restrict (Icc (collars index) 1), ∀ mode,
      curve radius mode = lowRhoPhysicalCoefficient parameters (collars index) (positive index) (fields index) radius mode)
    (K : ℝ) (estimate : ∀ index, ‖fields index‖ ≤ K)
include same decreasing cofinal estimate

/-- Uniform original weighted collar energies control the SAME global
physical Fourier curve divided by r, summing all angular and cell modes. -/
theorem physicalHilbertCurve_overRadius_global_energy :
    (∫⁻ radius, ENNReal.ofReal (‖radius⁻¹ • curve radius‖ ^ 2) ∂volume.restrict (Ioc 0 1)) ≤
      ENNReal.ofReal (K ^ 2) := by
  have bound := cofinalEnergy_bound 1 collars positive decreasing cofinal
    (fun radius => ENNReal.ofReal (‖radius⁻¹ • curve radius‖ ^ 2)) 0 (ENNReal.ofReal (K ^ 2)) (fun index => ?_)
  · simpa only [add_zero] using bound
  · rw [add_zero]
    calc
      _ ≤ ∫⁻ radius, physicalBulkSquare dimension (collars index) (fields index) radius
          ∂volume.restrict (Icc (collars index) 1) :=
        lintegral_mono_ae (physicalHilbertCurve_overRadius_square parameters (collars index) (positive index) (fields index) curve (same index))
      _ = ENNReal.ofReal (‖fields index‖ ^ 2) := physicalBulkSquare_integral dimension _ _
      _ ≤ ENNReal.ofReal (K ^ 2) := ENNReal.ofReal_le_ofReal
        ((sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (estimate index))).mpr (estimate index))

theorem physicalHilbertCurve_overRadius_memLp
    (measurable : AEStronglyMeasurable curve (volume.restrict (Ioc 0 1))) :
    MemLp (fun radius => radius⁻¹ • curve radius) 2 (volume.restrict (Ioc 0 1)) := by
  have dividedMeasurable : AEStronglyMeasurable (fun radius => radius⁻¹ • curve radius)
      (volume.restrict (Ioc 0 1)) := measurable_id.inv.aestronglyMeasurable.smul measurable
  apply (memLp_two_iff_integrable_sq_norm dividedMeasurable).mpr
  refine ⟨dividedMeasurable.norm.pow 2,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun _ => sq_nonneg _))).mpr
  exact (physicalHilbertCurve_overRadius_global_energy parameters collars positive decreasing cofinal fields curve same K estimate).trans_lt ENNReal.ofReal_lt_top

theorem physicalHilbertCurve_overRadius_integrable
    (measurable : AEStronglyMeasurable curve (volume.restrict (Ioc 0 1))) :
    Integrable (fun radius => radius⁻¹ • curve radius) (volume.restrict (Ioc 0 1)) :=
  (physicalHilbertCurve_overRadius_memLp parameters collars positive decreasing cofinal fields curve same K estimate measurable).integrable (by norm_num)

end Grad.WeightedAxisRemoval
