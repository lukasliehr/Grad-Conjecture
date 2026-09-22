import AKAE4SameCompatiblePhysicalGluing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceBoundaryTrace
open Grad.AnnularCurrentLow Grad.AnnularSmoothCore Grad.AnnularRestriction

/-- Exact selection of one axial Fourier cell; no angular truncation. -/
def cellPhysicalRow {dimension : ℕ} (lower : ℝ) (cell : ℤ) (row : DivisionRow dimension lower) : DivisionRow dimension lower :=
  ⟨fun mode => if mode.2=cell then row mode else 0,
    (lp.memℓp row).mono' (fun mode => by split_ifs <;> simp only [norm_zero,norm_nonneg,le_refl])⟩

theorem cellPhysicalRow_bound {dimension : ℕ} (lower : ℝ) (cell : ℤ) (row : DivisionRow dimension lower) :
    ‖cellPhysicalRow lower cell row‖ ≤ ‖row‖ := by
  apply lp.norm_mono (by norm_num)
  intro mode
  change ‖if mode.2=cell then row mode else 0‖ ≤ ‖row mode‖
  split_ifs <;> simp

theorem cellPhysicalRow_ae {dimension : ℕ} (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (cell : ℤ) (row : DivisionRow dimension lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),∀ mode,
      lowRhoPhysicalCoefficient parameters lower positive (cellPhysicalRow lower cell row) radius mode =
        if mode.2=cell then lowRhoPhysicalCoefficient parameters lower positive row radius mode else 0 := by
  filter_upwards [Lp.coeFn_zero (ComplexEuclidean dimension) 2 (volume.restrict (Icc lower 1))] with radius zero
  intro mode
  change _ • (if mode.2=cell then row mode else 0) radius = _
  split_ifs
  · rfl
  · rw [zero]
    exact smul_zero _

def cellHilbertProjection (parameters : PhaseParameters) (dimension : ℕ) (cell : ℤ) : CellL2 dimension →L[ℂ] CellL2 dimension :=
  boundedHilbertMultiplier parameters dimension (fun mode => if mode.2=cell then 1 else 0) 1 zero_le_one
    (fun mode => by split_ifs <;> norm_num)

variable {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

def SmoothLowPhysicalRow.cellProjection (cell : ℤ) : SmoothLowPhysicalRow parameters lower positive (cellPhysicalRow lower cell row) where
  curve grade radius := cellHilbertProjection parameters dimension cell (curves.curve grade radius)
  smooth grade := (cellHilbertProjection parameters dimension cell).restrictScalars ℝ |>.contDiff.comp_contDiffOn (curves.smooth grade)
  same grade := by
    filter_upwards [curves.same grade,cellPhysicalRow_ae parameters lower positive cell row] with radius same projected
    intro mode
    change (if mode.2=cell then (1 : ℂ) else 0) • curves.curve grade radius mode = _
    rw [same mode,projected mode]
    split_ifs <;> simp

theorem SmoothLowPhysicalRow.physicalCurve_cellProjection (bounded : lower < 1) (cell : ℤ) (grade : ℕ)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    (curves.cellProjection cell).physicalCurve grade radius mode =
      if mode.2=cell then curves.physicalCurve grade radius mode else 0 := by
  rw [(curves.cellProjection cell).physicalCurve_coefficient bounded grade radius inside mode,
    curves.physicalCurve_coefficient bounded grade radius inside mode]
  change _ • ((if mode.2=cell then (1 : ℂ) else 0) • curves.curve grade radius mode) = _
  split_ifs <;> simp

theorem cellPhysicalRow_restriction (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper)
    (cell : ℤ) (row : DivisionRow dimension lower) :
    originalBulkRestriction dimension lower upper included (cellPhysicalRow lower cell row) =
      cellPhysicalRow upper cell (originalBulkRestriction dimension lower upper included row) := by
  apply lp.ext
  funext mode
  change collarL2Restriction dimension lower upper included (if mode.2=cell then row mode else 0) =
    if mode.2=cell then collarL2Restriction dimension lower upper included (row mode) else 0
  split_ifs <;> simp

end Grad.ActualSmoothPhysicalField
