import ANR22CompletedPolarPairing
import ANR23RadialTestOperator

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.BoundaryTrace
open Grad.NonlinearDivision Grad.NonlinearQuotientBounds

private theorem corePairing_polar (first second : ClosedJet 1) :
    inner ℂ (closedL2Core first) (closedL2Core second) =
      ∫ radius in Icc (0 : ℝ) 1, ∫ angle in Icc (-Real.pi) Real.pi,
        radius • inner ℂ (smoothClosedExtension first (polarPlane (radius, angle)))
          (smoothClosedExtension second (polarPlane (radius, angle))) := by
  have actual := closedL2_inner_representatives first second
    (smoothClosedExtension first) (smoothClosedExtension second)
    (fun point => (smoothClosedExtension_value first point).symm)
    (fun point => (smoothClosedExtension_value second point).symm)
  have polar := closedDisk_polar_complex (fun point => inner ℂ (smoothClosedExtension first point) (smoothClosedExtension second point))
    ((smoothClosedExtension_smooth first).continuous.inner (smoothClosedExtension_smooth second).continuous)
  rw [Measure.restrict_congr_set closedUnitDisk_ae_openUnitDisk] at polar
  exact actual.trans polar

/-- Equality on all positive interior circles determines the actual ordinary
area L2 class, without selecting an argument at the axis or a polar cut. -/
theorem closedL2_eq_of_polar (first second : ClosedJet 1)
    (agree : ∀ radius : ℝ, ∀ inside : radius ∈ Ioo (0 : ℝ) 1, ∀ angle : ℝ,
      first.value (polarClosedPoint radius angle inside.1.le inside.2.le) =
        second.value (polarClosedPoint radius angle inside.1.le inside.2.le)) :
    closedL2Core first = closedL2Core second := by
  apply ext_inner_right ℂ
  intro field
  have firstContinuous : Continuous (fun field : DiskL2 1 => inner ℂ (closedL2Core first) field) := (innerSL ℂ _).continuous
  have secondContinuous : Continuous (fun field : DiskL2 1 => inner ℂ (closedL2Core second) field) := (innerSL ℂ _).continuous
  apply isClosed_property closedL2Core_denseRange (isClosed_eq firstContinuous secondContinuous) _ field
  intro core
  rw [corePairing_polar, corePairing_polar]
  have interior : ∀ᵐ radius : ℝ ∂volume.restrict (Icc (0 : ℝ) 1), radius ∈ Ioo (0 : ℝ) 1 := by
    have measureEquality : (volume : Measure ℝ).restrict (Icc (0 : ℝ) 1) = volume.restrict (Ioo (0 : ℝ) 1) :=
      Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
    rw [measureEquality]
    exact ae_restrict_mem measurableSet_Ioo
  apply integral_congr_ae
  filter_upwards [interior] with radius inside
  apply integral_congr_ae
  filter_upwards [] with angle
  have equality := (smoothClosedExtension_value first (polarClosedPoint radius angle inside.1.le inside.2.le)).trans
    ((agree radius inside angle).trans (smoothClosedExtension_value second (polarClosedPoint radius angle inside.1.le inside.2.le)).symm)
  exact congrArg (fun value : ComplexEuclidean 1 => radius • inner ℂ value (smoothClosedExtension core (polarPlane (radius, angle)))) equality

/-- Actual compact-test operator identity in the precise L2 carrier consumed
by the AN18 weak equation. -/
theorem radialTestJet_laplacianL2 (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (smooth : ContDiff ℝ ∞ test) (inside : tsupport test ⊆ Ioo (0 : ℝ) 1) :
    closedL2Core (laplacianJet (radialTestJet mode vector test smooth inside)) =
      closedL2Core (radialTestJet mode vector (radialTestOperator mode test)
        (radialTestOperator_smooth mode test smooth inside) ((radialTestOperator_support mode test).trans inside)) := by
  apply closedL2_eq_of_polar
  intro radius radiusIn angle
  exact (laplacianJet_global_literal (radialTestLift mode vector test)
    (radialTestLift_smooth mode vector test smooth inside)
    (polarClosedPoint radius angle radiusIn.1.le radiusIn.2.le)).trans
      (radialTestLift_laplacian_polar mode vector test smooth inside radius angle radiusIn)

end Grad.CircularHighRegularity
