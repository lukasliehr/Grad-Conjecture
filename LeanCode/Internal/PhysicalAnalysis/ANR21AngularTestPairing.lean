import ANR20ComplexPolarIntegral

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.BoundaryTrace

private theorem exponential_conjugate (mode : ℤ) (angle : ℝ) :
    starRingEnd ℂ (cellExponential mode angle) = cellExponential (-mode) angle := by
  unfold cellExponential
  rw [← Complex.exp_conj]
  congr 1
  simp [map_mul]

/-- Exact unnormalized angle integral versus the accepted Fourier coefficient. -/
theorem angular_inner_coefficient (mode : ℤ) (vector : ComplexEuclidean 1)
    (field : ℝ → ComplexEuclidean 1) (continuousField : Continuous field) :
    (∫ angle in Icc (-Real.pi) Real.pi, inner ℂ (cellExponential mode angle • vector) (field angle)) =
      (2 * Real.pi) • inner ℂ vector (angularCoefficient field mode) := by
  have integrable : IntegrableOn (fun angle => cellExponential (-mode) angle • field angle)
      (Icc (-Real.pi) Real.pi) :=
    ((cellExponential_smooth (-mode)).continuous.smul continuousField).continuousOn.integrableOn_Icc
  have mapped := (innerSL ℂ vector).integral_comp_comm (μ := volume.restrict (Icc (-Real.pi) Real.pi)) integrable
  have convertInner : (∫ angle in Icc (-Real.pi) Real.pi, inner ℂ (cellExponential mode angle • vector) (field angle)) =
      ∫ angle in Icc (-Real.pi) Real.pi, inner ℂ vector (cellExponential (-mode) angle • field angle) := by
    apply integral_congr_ae
    filter_upwards [] with angle
    rw [inner_smul_left, inner_smul_right, exponential_conjugate]
  have periodNonzero : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  exact convertInner.trans (mapped.trans (by
    rw [angularCoefficient_compact, inner_smul_right_eq_smul, smul_smul,
      mul_inv_cancel₀ periodNonzero, one_smul]
    rfl))

theorem radialTestLift_angle_pairing (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (field : ClosedJet 1) (radius : ℝ) (nonnegative : 0 ≤ radius) :
    (∫ angle in Icc (-Real.pi) Real.pi,
      radius • inner ℂ (radialTestLift mode vector test (polarPlane (radius, angle)))
        (smoothClosedExtension field (polarPlane (radius, angle)))) =
      (2 * Real.pi) • ((radius * test radius) •
        inner ℂ vector (radialCoefficientJet (originalPolarValue field) mode 0 radius)) := by
  by_cases zero : radius = 0
  · subst radius
    simp
  · have positive : 0 < radius := lt_of_le_of_ne nonnegative (Ne.symm zero)
    have expression : (fun angle => radius • inner ℂ (radialTestLift mode vector test (polarPlane (radius, angle)))
        (smoothClosedExtension field (polarPlane (radius, angle)))) =
        (fun angle => (radius * test radius) • inner ℂ (cellExponential mode angle • vector)
          (originalPolarValue field (radius, angle))) := by
      funext angle
      rw [radialTestLift_model mode vector test radius positive angle]
      change radius • inner ℂ (test radius • (cellExponential mode angle • vector))
        (originalPolarValue field (radius, angle)) = _
      rw [inner_smul_left_eq_smul, smul_smul]
    have coefficient := angular_inner_coefficient mode vector
      (fun angle => originalPolarValue field (radius, angle))
      ((originalPolarValue_smooth field).continuous.comp (continuous_const.prodMk continuous_id))
    rw [expression, integral_smul]
    exact (congrArg (fun value : ℂ => (radius * test radius) • value) coefficient).trans (smul_comm _ _ _)

theorem radialTestLift_core_pairing (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (smooth : ContDiff ℝ ∞ test) (supported : tsupport test ⊆ Ioo (0 : ℝ) 1) (field : ClosedJet 1) :
    inner ℂ (closedL2Core (globalClosedJet (radialTestLift mode vector test)
      (radialTestLift_smooth mode vector test smooth supported))) (closedL2Core field) =
      (2 * Real.pi) • ∫ radius in Icc (0 : ℝ) 1, (radius * test radius) •
        inner ℂ vector (radialCoefficientJet (originalPolarValue field) mode 0 radius) := by
  have actual := closedL2_inner_representatives
    (globalClosedJet (radialTestLift mode vector test) (radialTestLift_smooth mode vector test smooth supported))
    field (radialTestLift mode vector test)
    (smoothClosedExtension field) (fun _ => rfl) (fun point => (smoothClosedExtension_value field point).symm)
  have polar := closedDisk_polar_complex
    (fun point => inner ℂ (radialTestLift mode vector test point) (smoothClosedExtension field point))
    ((radialTestLift_smooth mode vector test smooth supported).continuous.inner
      (smoothClosedExtension_smooth field).continuous)
  rw [Measure.restrict_congr_set closedUnitDisk_ae_openUnitDisk] at polar
  exact actual.trans (polar.trans (by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
    exact radialTestLift_angle_pairing mode vector test field radius inside.1))

end Grad.CircularHighRegularity
