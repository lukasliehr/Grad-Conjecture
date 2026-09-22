import QuotientDotConsumer

noncomputable section

open Set
open scoped ContDiff

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct Grad.NonlinearRadial
open Grad.NonlinearQuotient Grad.PhysicalFamily

theorem laplacianCoefficient_global {dimension : ℕ}
    (field : SpatialPlane → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field) (point : ClosedDisk) :
    laplacianCoefficient (globalClosedJet field smooth) point = diskLaplacian field point.val := by
  unfold laplacianCoefficient
  rw [ContinuousMap.add_apply, globalClosedJet_derivative, globalClosedJet_derivative]
  simp only [cartesianDerivative, iteratedFDeriv_two_apply, diskLaplacian, Fin.sum_univ_two]
  rfl

theorem laplacianCore_smooth_coefficient {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (cell : ℤ) (point : ClosedDisk) :
    ((laplacianCore parameters field).val cell).value point =
      diskLaplacian (smoothClosedExtension (field.val cell)) point.val := by
  rw [laplacianCore_actual]
  have identity := laplacianCoefficient_global (smoothClosedExtension (field.val cell))
    (smoothClosedExtension_smooth (field.val cell)) point
  rw [smoothClosedExtension_restricts] at identity
  exact identity

/-- Immediate O11 consumer with the Laplacian now constructed in the actual
original core, not supplied as a separately assumed source field. The
radial/axis hypotheses are exactly the unchanged smooth division domain. -/
theorem actual_radial_laplacian_division {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (radius : ℝ) (collar : 1 < radius)
    (radial : ∀ cell angle point, point ∈ Metric.ball 0 radius →
      smoothClosedExtension (field.val cell) (planeRotationAction angle point) =
        smoothClosedExtension (field.val cell) point)
    (origin : ∀ cell, (field.val cell).value ⟨0, by simp [closedUnitDisk]⟩ = 0) :
    (∀ (cell : ℤ) (point : ClosedDisk), (field.val cell).value point =
      ‖point.val‖ ^ 2 • ((radialCore parameters (laplacianCore parameters field)).val cell).value point) ∧
    ∀ grade, originalGradeNorm grade (radialCore parameters (laplacianCore parameters field)) ≤
      dilationGradeConstant grade * laplacianGradeConstant grade * originalGradeNorm (grade + 2) field := by
  have division := radialCore_laplacian_consumer parameters (laplacianCore parameters field)
    (fun cell => smoothClosedExtension (field.val cell)) radius collar
    (fun cell => (smoothClosedExtension_smooth (field.val cell)).contDiffOn) radial
    (fun cell => (smoothClosedExtension_value (field.val cell) ⟨0, by simp [closedUnitDisk]⟩).trans (origin cell))
    (laplacianCore_smooth_coefficient parameters field)
  refine ⟨?_, ?_⟩
  · intro cell point
    exact (smoothClosedExtension_value (field.val cell) point).symm.trans (division.1 cell point)
  · intro grade
    exact (division.2 grade).trans
      ((mul_le_mul_of_nonneg_left (laplacianCore_bound parameters field grade)
        (dilationGradeConstant_nonnegative _)).trans_eq (mul_assoc _ _ _).symm)

end Grad.NonlinearQuotientBounds
