import ANR52ActualClosedCollarConsumer
import AIG2ActualGlobalGluing
import ANG25L2ModeConvergence

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

namespace Grad.ActualOuterCollar
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.ActualInverseInduction Grad.InteriorLocalization
open Grad.AnnularSourceGraph Grad.BoundaryLift

def outerCharacter (mode : ℤ) (point : SpatialPlane) : ℂ :=
  (outerCutoffScalar point : ℂ) * unitComplexCoordinate point ^ mode

theorem outerCutoff_zero_germ (point : SpatialPlane) (small : ‖point‖ < (7 / 12 : ℝ)) :
    outerCutoffScalar =ᶠ[𝓝 point] (fun _ => 0) := by
  filter_upwards [interiorCutoff_germ point small] with next same
  simp only [outerCutoffScalar, same, sub_self]

theorem outerCharacter_smooth (mode : ℤ) : ContDiff ℝ ∞ (outerCharacter mode) := by
  rw [contDiff_iff_contDiffAt]
  intro point
  by_cases small : ‖point‖ < (7 / 12 : ℝ)
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [outerCutoff_zero_germ point small] with next zero
    simp only [outerCharacter, zero, Complex.ofReal_zero, zero_mul]
  · have nonzero : point ≠ 0 := by intro zero; simp only [zero, norm_zero] at small; norm_num at small
    have unitNonzero : unitComplexCoordinate point ≠ 0 := by
      intro zero
      have normOne := unitComplexCoordinate_norm point nonzero
      rw [zero, norm_zero] at normOne
      norm_num at normOne
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp point outerCutoffScalar_smooth.contDiffAt).mul
      (contDiffAt_complex_zpow (unitComplexCoordinate_contDiffAt point nonzero) unitNonzero mode)

def outerRadialField (mode : ℤ) (profile : ℝ → ComplexEuclidean 1)
    (point : SpatialPlane) : ComplexEuclidean 1 :=
  outerCharacter mode point • profile ‖point‖

theorem outerRadialField_zero_germ (mode : ℤ) (profile : ℝ → ComplexEuclidean 1)
    (point : SpatialPlane) (small : ‖point‖ < (7 / 12 : ℝ)) :
    outerRadialField mode profile =ᶠ[𝓝 point] (fun _ => 0) := by
  filter_upwards [outerCutoff_zero_germ point small] with next zero
  simp only [outerRadialField, outerCharacter, zero, Complex.ofReal_zero, zero_mul, zero_smul]

theorem outerRadialField_smooth (mode : ℤ) (profile : ℝ → ComplexEuclidean 1)
    (smooth : ContDiffOn ℝ ∞ profile (Icc (1 / 2 : ℝ) 1)) :
    ContDiffOn ℝ ∞ (outerRadialField mode profile) closedUnitDisk := by
  intro point inside
  by_cases small : ‖point‖ < (7 / 12 : ℝ)
  · exact ((contDiffAt_const (c := (0 : ComplexEuclidean 1))).congr_of_eventuallyEq
      (outerRadialField_zero_germ mode profile point small)).contDiffWithinAt
  · have lower : (1 / 2 : ℝ) < ‖point‖ := by linarith [not_lt.mp small]
    have nonzero : point ≠ 0 := norm_pos_iff.mp (lt_trans (by norm_num) lower)
    have normSmooth : ContDiffWithinAt ℝ ∞ (fun next : SpatialPlane => ‖next‖) closedUnitDisk point :=
      (contDiffAt_norm ℝ nonzero).contDiffWithinAt
    have normMaps : MapsTo (fun next : SpatialPlane => ‖next‖)
        (closedUnitDisk ∩ {next | (1 / 2 : ℝ) < ‖next‖}) (Icc (1 / 2 : ℝ) 1) :=
      fun _ member => ⟨member.2.le, member.1⟩
    have profileSmooth := (smooth ‖point‖ ⟨lower.le, inside⟩).comp point
      (normSmooth.mono inter_subset_left) normMaps
    have product := (outerCharacter_smooth mode).contDiffAt.contDiffWithinAt.smul profileSmooth
    exact product.mono_of_mem_nhdsWithin (inter_mem_nhdsWithin _
      ((isOpen_lt continuous_const continuous_norm).mem_nhds lower))

end Grad.ActualOuterCollar
