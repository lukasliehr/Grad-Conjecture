import AngularCoordinateShift
import PolarAngularMean
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

noncomputable section

namespace Grad.Constraints

open Grad.ClosedJets

theorem signedComplexCoordinate_one_norm (point : SpatialPlane) :
    ‖signedComplexCoordinate 1 point‖ = ‖point‖ := by
  rw [Complex.norm_def, PiLp.norm_eq_of_L2]
  simp [signedComplexCoordinate, Complex.normSq_apply, Fin.sum_univ_two,
    Real.norm_eq_abs, pow_two]

/-- The polar formulas cover the entire closed disk, not a chosen angular
sector. They are valid at radius zero too, although no polar basis at the
origin is used to define any Cartesian operator. -/
theorem closedPoint_has_polar_angle (point : ClosedDisk) :
    ∃ angle : ℝ, polarClosedPoint ‖point.val‖
      (by rw [abs_norm]; exact point.property) angle = point := by
  refine ⟨Complex.arg (signedComplexCoordinate 1 point.val), ?_⟩
  apply Subtype.ext
  rw [polarClosedPoint_coordinates]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · change ‖point.val‖ * Real.cos (Complex.arg (signedComplexCoordinate 1 point.val)) = point.val 0
    rw [← signedComplexCoordinate_one_norm]
    rw [Complex.norm_mul_cos_arg]
    simp [signedComplexCoordinate]
  · change ‖point.val‖ * Real.sin (Complex.arg (signedComplexCoordinate 1 point.val)) = point.val 1
    rw [← signedComplexCoordinate_one_norm]
    rw [Complex.norm_mul_sin_arg]
    simp [signedComplexCoordinate]

theorem tangentialJet_every_nonzero_point (field : ClosedJet 2) (point : ClosedDisk)
    (nonzero : point.val ≠ 0) :
    0 < ‖point.val‖ ∧ ∃ angle : ℝ,
      polarClosedPoint ‖point.val‖ (by rw [abs_norm]; exact point.property) angle = point ∧
      (tangentialJet field).value point =
        polarTangentialMean field ‖point.val‖ (by rw [abs_norm]; exact point.property) angle •
          polarTangentialVector angle := by
  obtain ⟨angle, equality⟩ := closedPoint_has_polar_angle point
  refine ⟨norm_pos_iff.mpr nonzero, angle, equality, ?_⟩
  have formula := tangentialJet_polar_formula field ‖point.val‖
    (by rw [abs_norm]; exact point.property) angle
  simpa only [equality] using formula

end Grad.Constraints
