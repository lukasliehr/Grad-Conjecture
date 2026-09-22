import ARW1ActualPolarField

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators
namespace Grad.ActualRadialWords
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.ActualOuterCollar Grad.ClosedDiskRegularity Grad.CollarCartesian Grad.BoundaryLift Grad.BoundaryTrace
open Grad.AnnularSourceGraph Grad.ActualInverseInduction Grad.InteriorLocalization

def actualPolarCutoff (point : ℝ × ℝ) : ℝ := outerCutoffScalar (collarPlane point)

theorem actualPolarCutoff_smooth : ContDiff ℝ ∞ actualPolarCutoff :=
  outerCutoffScalar_smooth.comp collarPlane_smooth

theorem collar_character (mode : ℤ) (point : ℝ × ℝ) (inside : point ∈ openHalfCollar) :
    unitComplexCoordinate (collarPlane point) ^ mode = cellExponential mode point.2 := by
  have positive : 0 < 1 - point.1 := by linarith [inside.1.2]
  have polar : collarPlane point = (1 - point.1) • boundaryCirclePoint (point.2 : CellCircle) := by
    rw [boundaryCirclePoint_coe]
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp [collarPlane]
  rw [polar, unitComplexCoordinate_polar (1 - point.1) positive, circle_zpow_fourier]
  exact cellCharacter_coe _ _

theorem actualFiniteOuter_polar (modes : Finset ℤ) (parameter : ℝ) (source : highDiskL2)
    (point : ℝ × ℝ) (inside : point ∈ openHalfCollar) :
    finiteOuterField modes parameter source (collarPlane point) =
      actualPolarCutoff point • actualPolarFinite modes parameter source point := by
  have positive : 0 < 1 - point.1 := by linarith [inside.1.2]
  simp only [finiteOuterField, actualPolarFinite, Finset.sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro mode _
  change outerRadialField mode (actualProfile mode parameter source) (collarPlane point) = _
  rw [outerRadialField, outerCharacter, collar_character mode point inside,
    collarPlane_norm, abs_of_pos positive, mul_smul, Complex.coe_smul]
  rfl

theorem actualOuterExtension_value (modes : Finset ℤ) (parameter : ℝ) (source : highDiskL2)
    (core : ClosedJet 1) (same : source.val = closedL2Core core)
    (point : SpatialPlane) (inside : point ∈ closedUnitDisk) :
    smoothClosedExtension (actualOuterJet modes parameter source core same) point =
      finiteOuterField modes parameter source point := by
  exact (smoothClosedExtension_value (actualOuterJet modes parameter source core same) ⟨point, inside⟩).trans rfl

theorem actualOuterExtension_zero (modes : Finset ℤ) (parameter : ℝ) (source : highDiskL2)
    (core : ClosedJet 1) (same : source.val = closedL2Core core)
    (point : SpatialPlane) (small : ‖point‖ < (7 / 12 : ℝ)) :
    smoothClosedExtension (actualOuterJet modes parameter source core same) point = 0 := by
  rw [actualOuterExtension_value modes parameter source core same point (by change ‖point‖ ≤ 1; linarith)]
  apply Finset.sum_eq_zero
  intro mode _
  exact (outerRadialField_zero_germ mode _ point small).eq_of_nhds

theorem actualOuterExtension_polar_germ (modes : Finset ℤ) (parameter : ℝ) (source : highDiskL2)
    (core : ClosedJet 1) (same : source.val = closedL2Core core)
    (point : ℝ × ℝ) (inside : point ∈ openHalfCollar) :
    (smoothClosedExtension (actualOuterJet modes parameter source core same) ∘ collarPlane) =ᶠ[𝓝 point]
      (fun next => actualPolarCutoff next • actualPolarFinite modes parameter source next) := by
  filter_upwards [openHalfCollar_open.mem_nhds inside] with next nextIn
  have member : collarPlane next ∈ closedUnitDisk := by
    change ‖collarPlane next‖ ≤ 1
    rw [collarPlane_norm, abs_of_pos (by linarith [nextIn.1.2] : 0 < 1 - next.1)]
    linarith [nextIn.1.1]
  exact (actualOuterExtension_value modes parameter source core same _ member).trans
    (actualFiniteOuter_polar modes parameter source next nextIn)

end Grad.ActualRadialWords
