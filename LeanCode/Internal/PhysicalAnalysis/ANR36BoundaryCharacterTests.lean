import ANR35RadialBoundaryTrace

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.BoundaryTrace Grad.BoundaryLift

/-- Character tests may have arbitrary outer boundary value. Only a
neighborhood of the axis is removed to make the Cartesian lift smooth. -/
theorem radialTestLift_smooth_away_axis (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (smooth : ContDiff ℝ ∞ test) (away : (0 : ℝ) ∉ tsupport test) :
    ContDiff ℝ ∞ (radialTestLift mode vector test) := by
  rw [contDiff_iff_contDiffAt]
  intro point
  by_cases zero : point = 0
  · subst point
    have profileZero : ∀ᶠ radius in 𝓝 (0 : ℝ), test radius = 0 := by
      filter_upwards [(isClosed_tsupport test).isOpen_compl.mem_nhds away] with radius outside
      exact image_eq_zero_of_notMem_tsupport outside
    have radiusZero : ∀ᶠ point : SpatialPlane in 𝓝 0, test ‖point‖ = 0 :=
      (continuous_norm.tendsto (0 : SpatialPlane)).eventually (by simpa only [norm_zero] using profileZero)
    apply (contDiffAt_const (c := (0 : ComplexEuclidean 1))).congr_of_eventuallyEq
    filter_upwards [radiusZero] with point zeroAt
    simp only [radialTestLift, zeroAt, Complex.ofReal_zero, zero_mul, zero_smul]
  · have normSmooth : ContDiffAt ℝ ∞ (fun point : SpatialPlane => ‖point‖) point := contDiffAt_norm ℝ zero
    have unitNonzero : unitComplexCoordinate point ≠ 0 := by
      intro vanished
      have normOne := unitComplexCoordinate_norm point zero
      rw [vanished, norm_zero] at normOne
      norm_num at normOne
    exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp point (smooth.contDiffAt.comp point normSmooth)).mul
      (contDiffAt_complex_zpow (unitComplexCoordinate_contDiffAt point zero) unitNonzero mode)).smul contDiffAt_const

def boundaryCharacterJet (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (smooth : ContDiff ℝ ∞ test) (away : (0 : ℝ) ∉ tsupport test) : ClosedJet 1 :=
  globalClosedJet (radialTestLift mode vector test) (radialTestLift_smooth_away_axis mode vector test smooth away)

theorem boundaryCharacterJet_core_pairing (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (smooth : ContDiff ℝ ∞ test) (away : (0 : ℝ) ∉ tsupport test) (field : ClosedJet 1) :
    inner ℂ (closedL2Core (boundaryCharacterJet mode vector test smooth away)) (closedL2Core field) =
      (2 * Real.pi) • ∫ radius in Icc (0 : ℝ) 1, (radius * test radius) •
        inner ℂ vector (radialCoefficientJet (originalPolarValue field) mode 0 radius) := by
  have actual := closedL2_inner_representatives (boundaryCharacterJet mode vector test smooth away)
    field (radialTestLift mode vector test) (smoothClosedExtension field)
    (fun _ => rfl) (fun point => (smoothClosedExtension_value field point).symm)
  have polar := closedDisk_polar_complex
    (fun point => inner ℂ (radialTestLift mode vector test point) (smoothClosedExtension field point))
    ((radialTestLift_smooth_away_axis mode vector test smooth away).continuous.inner
      (smoothClosedExtension_smooth field).continuous)
  rw [Measure.restrict_congr_set closedUnitDisk_ae_openUnitDisk] at polar
  exact actual.trans (polar.trans (by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
    exact radialTestLift_angle_pairing mode vector test field radius inside.1))

end Grad.CircularHighRegularity
