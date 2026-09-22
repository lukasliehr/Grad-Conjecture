import AIC2ActualCellLocalization

noncomputable section
open MeasureTheory
open scoped ContDiff Topology

namespace Grad.InteriorLocalization
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.WeightedJets Grad.CompactCutoff

/-- A fixed interior cutoff: one through radius7/12 and zero beyond2/3.
The annulus carrying its derivatives is separated from both axis and boundary. -/
def interiorCutoff := diskCutoff (1 / 2 : ℝ) (1 / 12 : ℝ) (by norm_num) (by norm_num)

theorem interiorCutoff_support : tsupport interiorCutoff.toFun =
    Metric.closedBall (0 : Grad.PDEBootstrap.Spatial) (2 / 3) := by
  simpa only [interiorCutoff, show (1 / 2 : ℝ) + 2 * (1 / 12) = 2 / 3 by norm_num] using
    diskCutoff_support (1 / 2 : ℝ) (1 / 12 : ℝ) (by norm_num) (by norm_num)

theorem interiorCutoff_supported : tsupport interiorCutoff.toFun ⊆ openUnitDisk := by
  rw [interiorCutoff_support]
  intro point member
  have normBound : ‖point‖ ≤ (2 / 3 : ℝ) := by simpa only [Metric.mem_closedBall, dist_zero_right] using member
  change ‖point‖ < 1
  linarith

theorem interiorCutoff_one : Set.EqOn interiorCutoff.toFun (fun _ => 1)
    (Metric.closedBall (0 : Grad.PDEBootstrap.Spatial) (7 / 12)) := by
  simpa only [interiorCutoff, show (1 / 2 : ℝ) + 1 / 12 = 7 / 12 by norm_num] using
    diskCutoff_one (1 / 2 : ℝ) (1 / 12 : ℝ) (by norm_num) (by norm_num)

theorem interiorCutoff_germ (point : Grad.PDEBootstrap.Spatial) (inside : ‖point‖ < (7 / 12 : ℝ)) :
    interiorCutoff.toFun =ᶠ[𝓝 point] (fun _ => 1) := by
  apply diskCutoff_germ (1 / 2 : ℝ) (1 / 12 : ℝ) (by norm_num) (by norm_num)
  simpa only [Metric.mem_ball, dist_zero_right, show (1 / 2 : ℝ) + 1 / 12 = 7 / 12 by norm_num] using inside

def interiorAPCell (L sigma gamma ell : ℝ) (dimension grade : ℕ) (cell : ℤ) :
    apGrade L sigma gamma ell dimension grade →L[ℂ] WJet dimension grade Set.univ (fun _ => 0) :=
  apCellLocalized L sigma gamma ell dimension grade cell interiorCutoff.toFun interiorCutoff.smooth
    interiorCutoff.compact interiorCutoff_supported

theorem interiorAPCell_bound (L sigma gamma ell : ℝ) (dimension grade : ℕ) (cell : ℤ)
    (field : apGrade L sigma gamma ell dimension grade) :
    ‖interiorAPCell L sigma gamma ell dimension grade cell field‖ ≤
      apCellLocalizationConstant L sigma gamma ell dimension grade cell interiorCutoff.toFun
        interiorCutoff.smooth interiorCutoff.compact * ‖field‖ :=
  apCellLocalized_norm_le L sigma gamma ell dimension grade cell _ _ _ _ field

end Grad.InteriorLocalization
