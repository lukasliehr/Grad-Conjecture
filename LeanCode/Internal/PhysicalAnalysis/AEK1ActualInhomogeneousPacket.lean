import AEG11ExactEnergyPacketConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal

namespace Grad.AnnularCurrentSource

open Grad.ClosedJets Grad.SourceCollarDivision Grad.AnnularCurrentEnergy

/-- The four independent normalized bulk inputs in the literal AHW order
`(F0, RF0, F2, f)`.  In particular the second coordinate is stored and
normed independently at this level. -/
abbrev HighKnownSourceBulk (lower : ℝ) :=
  PiLp 2 (fun _ : Fin 4 => DivisionRow 1 lower)

def highSourceF0 (lower : ℝ) :
    HighKnownSourceBulk lower →L[ℂ] DivisionRow 1 lower :=
  PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 4 => DivisionRow 1 lower) 0

def highSourceRF0 (lower : ℝ) :
    HighKnownSourceBulk lower →L[ℂ] DivisionRow 1 lower :=
  PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 4 => DivisionRow 1 lower) 1

def highSourceF2 (lower : ℝ) :
    HighKnownSourceBulk lower →L[ℂ] DivisionRow 1 lower :=
  PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 4 => DivisionRow 1 lower) 2

def highSourceF (lower : ℝ) :
    HighKnownSourceBulk lower →L[ℂ] DivisionRow 1 lower :=
  PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 4 => DivisionRow 1 lower) 3

/-- Literal inhomogeneous input for AHW.  Slots zero through three are
untouched and the four source coordinates occupy slots four through seven. -/
def highKnownEightPacket (lower : ℝ) :
    HighKnownSourceBulk lower →L[ℂ] DivisionRow 8 lower :=
  (bulkMatrixUnit lower 4 0).comp (highSourceF0 lower) +
  (bulkMatrixUnit lower 5 0).comp (highSourceRF0 lower) +
  (bulkMatrixUnit lower 6 0).comp (highSourceF2 lower) +
  (bulkMatrixUnit lower 7 0).comp (highSourceF lower)

theorem highKnownSourceBulk_norm_sq (lower : ℝ)
    (source : HighKnownSourceBulk lower) :
    ‖source‖ ^ 2 = ‖source 0‖ ^ 2 + ‖source 1‖ ^ 2 +
      ‖source 2‖ ^ 2 + ‖source 3‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_four]

private theorem highKnownSourceBulk_coordinate_bound (lower : ℝ)
    (source : HighKnownSourceBulk lower) (coordinate : Fin 4) :
    ‖source coordinate‖ ≤ ‖source‖ := by
  have squared : ‖source coordinate‖ ^ 2 ≤ ∑ index : Fin 4, ‖source index‖ ^ 2 :=
    Finset.single_le_sum (fun index _ => sq_nonneg ‖source index‖) (Finset.mem_univ coordinate)
  rw [← PiLp.norm_sq_eq_of_L2] at squared
  exact (sq_le_sq₀ (norm_nonneg (source coordinate)) (norm_nonneg source)).mp squared

theorem highKnownEightPacket_bound (lower : ℝ)
    (source : HighKnownSourceBulk lower) :
    ‖highKnownEightPacket lower source‖ ≤ 4 * ‖source‖ := by
  have first := (bulkMatrixUnit_bound lower (4 : Fin 8) (0 : Fin 1) (source 0)).trans
    (highKnownSourceBulk_coordinate_bound lower source 0)
  have second := (bulkMatrixUnit_bound lower (5 : Fin 8) (0 : Fin 1) (source 1)).trans
    (highKnownSourceBulk_coordinate_bound lower source 1)
  have third := (bulkMatrixUnit_bound lower (6 : Fin 8) (0 : Fin 1) (source 2)).trans
    (highKnownSourceBulk_coordinate_bound lower source 2)
  have fourth := (bulkMatrixUnit_bound lower (7 : Fin 8) (0 : Fin 1) (source 3)).trans
    (highKnownSourceBulk_coordinate_bound lower source 3)
  calc
    _ ≤ ‖bulkMatrixUnit lower (4 : Fin 8) (0 : Fin 1) (source 0)‖ +
        ‖bulkMatrixUnit lower (5 : Fin 8) (0 : Fin 1) (source 1)‖ +
        ‖bulkMatrixUnit lower (6 : Fin 8) (0 : Fin 1) (source 2)‖ +
        ‖bulkMatrixUnit lower (7 : Fin 8) (0 : Fin 1) (source 3)‖ :=
      (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ ‖source‖ + ‖source‖ + ‖source‖ + ‖source‖ :=
      add_le_add (add_le_add (add_le_add first second) third) fourth
    _ = 4 * ‖source‖ := by ring

end Grad.AnnularCurrentSource
