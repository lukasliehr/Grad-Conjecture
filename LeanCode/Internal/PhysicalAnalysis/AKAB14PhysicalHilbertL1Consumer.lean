import AKAB13GlobalPhysicalHilbertIntegrability

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Grad.WeightedAxisRemoval
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.AnnularCurrentLow

variable {dimension : ℕ} (parameters : PhaseParameters) (collars : ℕ → ℝ)
    (positive : ∀ index, 0 < collars index) (decreasing : Antitone collars)
    (cofinal : Tendsto collars atTop (𝓝 0))
    (fields : ∀ index, DivisionRow dimension (collars index)) (curve : ℝ → CellL2 dimension)
    (same : ∀ index, ∀ᵐ radius ∂volume.restrict (Icc (collars index) 1), ∀ mode,
      curve radius mode = lowRhoPhysicalCoefficient parameters (collars index) (positive index) (fields index) radius mode)
    (K : ℝ) (estimate : ∀ index, ‖fields index‖ ≤ K)
    (measurable : AEStronglyMeasurable curve (volume.restrict (Ioc 0 1)))
include same decreasing cofinal estimate measurable

theorem physicalHilbertCurve_memLp : MemLp curve 2 (volume.restrict (Ioc 0 1)) := by
  have divided := physicalHilbertCurve_overRadius_memLp parameters collars positive decreasing cofinal fields curve same K estimate measurable
  apply divided.of_le measurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with radius inside
  have recovery : radius • (radius⁻¹ • curve radius) = curve radius := by
    rw [smul_smul,mul_inv_cancel₀ inside.1.ne',one_smul]
  have norms := congrArg norm recovery
  rw [norm_smul,Real.norm_of_nonneg inside.1.le] at norms
  exact norms.symm.trans_le (mul_le_of_le_one_left (norm_nonneg _) inside.2)

/-- The exact global physical Hilbert curve and its division by r are
integrable. This is the input for the ordinary Cartesian polar/Fourier
change of coordinates in the axis-removal consumer. -/
theorem physicalHilbertCurve_integrable_pair :
    Integrable curve (volume.restrict (Ioc 0 1)) ∧
      Integrable (fun radius => radius⁻¹ • curve radius) (volume.restrict (Ioc 0 1)) :=
  ⟨(physicalHilbertCurve_memLp parameters collars positive decreasing cofinal fields curve same K estimate measurable).integrable (by norm_num),
    physicalHilbertCurve_overRadius_integrable parameters collars positive decreasing cofinal fields curve same K estimate measurable⟩

theorem physicalHilbertCurve_norm_overRadius_integrable :
    Integrable (fun radius => radius⁻¹ * ‖curve radius‖) (volume.restrict (Ioc 0 1)) := by
  have divided := (physicalHilbertCurve_overRadius_integrable parameters collars positive decreasing cofinal fields curve same K estimate measurable).norm
  apply divided.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with radius inside
  rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr inside.1.le)]

end Grad.WeightedAxisRemoval
