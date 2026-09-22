import AIR1UniformActualSourceRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularKnownLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularCurrentLow
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource Grad.AnnularReconstruction Grad.AnnularKernelL2

/-- The original known source tuple: every homogeneous retained input is zero. -/
def knownLowSevenPacket (lower : ℝ) : HighKnownSourceBulk lower →L[ℂ] DivisionRow 7 lower :=
  (bulkMatrixUnit lower 4 0).comp (highSourceF0 lower) +
  (bulkMatrixUnit lower 5 0).comp (highSourceRF0 lower) +
  (bulkMatrixUnit lower 6 0).comp (highSourceF2 lower)

theorem knownBulk_coordinate_bound (lower : ℝ) (source : HighKnownSourceBulk lower) (slot : Fin 4) :
    ‖source slot‖ ≤ ‖source‖ := by
  have square : ‖source slot‖ ^ 2 ≤ ∑ index : Fin 4, ‖source index‖ ^ 2 :=
    Finset.single_le_sum (fun index _ => sq_nonneg ‖source index‖) (Finset.mem_univ slot)
  rw [← PiLp.norm_sq_eq_of_L2] at square
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp square

theorem knownLowSevenPacket_bound (lower : ℝ) (source : HighKnownSourceBulk lower) :
    ‖knownLowSevenPacket lower source‖ ≤ 3 * ‖source‖ := by
  have first := (bulkMatrixUnit_bound lower (4 : Fin 7) (0 : Fin 1) (source 0)).trans (knownBulk_coordinate_bound lower source 0)
  have second := (bulkMatrixUnit_bound lower (5 : Fin 7) (0 : Fin 1) (source 1)).trans (knownBulk_coordinate_bound lower source 1)
  have third := (bulkMatrixUnit_bound lower (6 : Fin 7) (0 : Fin 1) (source 2)).trans (knownBulk_coordinate_bound lower source 2)
  change ‖bulkMatrixUnit lower (4 : Fin 7) (0 : Fin 1) (source 0) +
    bulkMatrixUnit lower (5 : Fin 7) (0 : Fin 1) (source 1) +
    bulkMatrixUnit lower (6 : Fin 7) (0 : Fin 1) (source 2)‖ ≤ _
  apply (norm_add_le _ _).trans
  exact (add_le_add (norm_add_le _ _) le_rfl).trans (by linarith)

/-- Literal AE original input; no datum or source is duplicated. -/
theorem knownLowSevenPacket_ae (lower : ℝ) (source : HighKnownSourceBulk lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      knownLowSevenPacket lower source mode radius =
        (source 0 mode radius 0) • Grad.GaugeCoefficients.Physical.Ledger.operatorBasis 4 +
        (source 1 mode radius 0) • Grad.GaugeCoefficients.Physical.Ledger.operatorBasis 5 +
        (source 2 mode radius 0) • Grad.GaugeCoefficients.Physical.Ledger.operatorBasis 6 := by
  rw [ae_all_iff]
  intro mode
  let first : DivisionRow 7 lower := bulkMatrixUnit lower 4 0 (source 0)
  let second : DivisionRow 7 lower := bulkMatrixUnit lower 5 0 (source 1)
  let third : DivisionRow 7 lower := bulkMatrixUnit lower 6 0 (source 2)
  have exactSum : knownLowSevenPacket lower source = first + second + third := rfl
  rw [exactSum]
  filter_upwards [bulkMatrixUnit_ae lower (4 : Fin 7) (0 : Fin 1) (source 0),
    bulkMatrixUnit_ae lower (5 : Fin 7) (0 : Fin 1) (source 1),
    bulkMatrixUnit_ae lower (6 : Fin 7) (0 : Fin 1) (source 2),
    Lp.coeFn_add (first mode) (second mode),
    Lp.coeFn_add (first mode + second mode) (third mode)] with radius one two three sum12 sum123
  change ((first mode + second mode) + third mode) radius = _
  have h12 : (first mode + second mode) radius = first mode radius + second mode radius := sum12
  have h123 : (first mode + second mode + third mode) radius = (first mode + second mode) radius + third mode radius := sum123
  exact h123.trans (congrArg₂ (fun a b : ComplexEuclidean 7 => a + b)
    (h12.trans (congrArg₂ (fun a b : ComplexEuclidean 7 => a + b) (one mode) (two mode))) (three mode))

end Grad.AnnularKnownLow
