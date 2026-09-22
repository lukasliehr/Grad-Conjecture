import AEK3ActualSourceGraphBulk
import AEJ6OnePhysicalHighFormBall

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal

namespace Grad.AnnularCurrentSource

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularCurrentEnergy
open Grad.AnnularKernelL2

/-- The remaining literal weighted bulk sources `(g,q_c,r q_v)`.  These are kept
independent of the two genuine radial source graphs. -/
abbrev HighAuxiliarySourceBulk (lower : ℝ) :=
  PiLp 2 (fun _ : Fin 3 => DivisionRow 1 lower)

def highSourceG (lower : ℝ) :
    HighAuxiliarySourceBulk lower →L[ℂ] DivisionRow 1 lower :=
  PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 => DivisionRow 1 lower) 0

def highSourceQc (lower : ℝ) :
    HighAuxiliarySourceBulk lower →L[ℂ] DivisionRow 1 lower :=
  PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 => DivisionRow 1 lower) 1

def highSourceRqv (lower : ℝ) :
    HighAuxiliarySourceBulk lower →L[ℂ] DivisionRow 1 lower :=
  PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 => DivisionRow 1 lower) 2

private theorem auxiliary_coordinate_bound (lower : ℝ)
    (source : HighAuxiliarySourceBulk lower) (coordinate : Fin 3) :
    ‖source coordinate‖ ≤ ‖source‖ := by
  have squared : ‖source coordinate‖ ^ 2 ≤ ∑ index : Fin 3, ‖source index‖ ^ 2 :=
    Finset.single_le_sum (fun index _ => sq_nonneg ‖source index‖)
      (Finset.mem_univ coordinate)
  rw [← PiLp.norm_sq_eq_of_L2] at squared
  exact (sq_le_sq₀ (norm_nonneg (source coordinate)) (norm_nonneg source)).mp squared

/-- Multiplication by the physical radius on the completed scalar row. -/
def radialRadiusRow (lower : ℝ) (positive : 0 < lower) :
    DivisionRow 1 lower →L[ℂ] DivisionRow 1 lower :=
  complexLpTwoMap
    (fun _ => scalarRadialMap lower ⟨fun radius => radius, continuous_id⟩ 1
      (fun radius inside => by
        change |radius| ≤ 1
        rw [abs_of_nonneg (positive.le.trans inside.1)]
        exact inside.2))
    1 zero_le_one (fun _ field => by
      simpa only [one_mul] using scalarRadialMap_bound lower
        ⟨fun radius => radius, continuous_id⟩ 1
        (fun radius inside => by
          change |radius| ≤ 1
          rw [abs_of_nonneg (positive.le.trans inside.1)]
          exact inside.2) field)

theorem radialRadiusRow_bound (lower : ℝ) (positive : 0 < lower)
    (field : DivisionRow 1 lower) :
    ‖radialRadiusRow lower positive field‖ ≤ ‖field‖ := by
  simpa only [radialRadiusRow, one_mul] using complexLpTwoMap_bound
    (fun _ : ℤ × ℤ => scalarRadialMap lower ⟨fun radius => radius, continuous_id⟩ 1
      (fun radius inside => by
        change |radius| ≤ 1
        rw [abs_of_nonneg (positive.le.trans inside.1)]
        exact inside.2))
    1 zero_le_one (fun _ field => by
      simpa only [one_mul] using scalarRadialMap_bound lower
        ⟨fun radius => radius, continuous_id⟩ 1
        (fun radius inside => by
          change |radius| ≤ 1
          rw [abs_of_nonneg (positive.le.trans inside.1)]
          exact inside.2) field) field

/-- The direct AI14/BF13 output rows.  They are literally
`(0,q_c,r q_v-r g)`, ready to pair with `(psi_r,psi_zeta/L,Rpsi/r)`.
The `L⁻¹` factor is already in the accepted test packet. -/
def directKnownThreePacket (lower : ℝ) (positive : 0 < lower) :
    HighAuxiliarySourceBulk lower →L[ℂ] DivisionRow 3 lower :=
  (bulkMatrixUnit lower 1 0).comp (highSourceQc lower) +
  (bulkMatrixUnit lower 2 0).comp
      (highSourceRqv lower - (radialRadiusRow lower positive).comp (highSourceG lower))

theorem directKnownThreePacket_bound (lower : ℝ) (positive : 0 < lower)
    (source : HighAuxiliarySourceBulk lower) :
    ‖directKnownThreePacket lower positive source‖ ≤ 3 * ‖source‖ := by
  have g := auxiliary_coordinate_bound lower source 0
  have qc := auxiliary_coordinate_bound lower source 1
  have qv := auxiliary_coordinate_bound lower source 2
  have radialG := (radialRadiusRow_bound lower positive (source 0)).trans g
  have thirdRow := (norm_sub_le (source 2)
    (radialRadiusRow lower positive (source 0))).trans (add_le_add qv radialG)
  have first := (bulkMatrixUnit_bound lower (1 : Fin 3) (0 : Fin 1) (source 1)).trans qc
  have second := (bulkMatrixUnit_bound lower (2 : Fin 3) (0 : Fin 1)
    (source 2 - radialRadiusRow lower positive (source 0))).trans thirdRow
  change ‖bulkMatrixUnit lower (1 : Fin 3) (0 : Fin 1) (source 1) +
    bulkMatrixUnit lower (2 : Fin 3) (0 : Fin 1)
      (source 2 - radialRadiusRow lower positive (source 0))‖ ≤ 3 * ‖source‖
  exact (norm_add_le _ _).trans (by nlinarith only [first, second])

/-- The complete known bulk output before testing: AHW acts at literal
power zero on `(F0,RF0,F2,f)`, while `g,q_c,q_v` enter directly with the
AI14 signs and radius factors. -/
def actualHighKnownBulkOutput (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : Grad.AnnularReconstruction.RetainedInverseState parameters L compact)
    (known : HighKnownSourceBulk lower)
    (auxiliary : HighAuxiliarySourceBulk lower) : DivisionRow 3 lower :=
  eliminatedBulkAction parameters L compact lower positive bounded state 0
      (highKnownEightPacket lower known) +
    directKnownThreePacket lower positive auxiliary

end Grad.AnnularCurrentSource
