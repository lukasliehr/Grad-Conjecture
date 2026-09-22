import BL26FiniteNorm

noncomputable section

open Set Filter
open scoped BigOperators Topology

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

theorem finiteBoundaryToGrade_apply {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (values : FiniteBoundaryData dimension) (output : ℤ × ℤ) :
    finiteBoundaryToGrade parameters grade gradePositive values output =
      (boundaryWeight parameters grade output : ℂ) • values output.2 output.1 := by
  rw [← boundary_weighted_coefficient parameters grade
    (finiteBoundaryToGrade parameters grade gradePositive values) output, finiteBoundaryToGrade_coefficient]

theorem finiteBoundaryToGrade_single {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (mode : ℤ × ℤ) (value : ComplexEuclidean dimension) :
    finiteBoundaryToGrade parameters grade gradePositive
      (Finsupp.single mode.2 (Finsupp.single mode.1 ((boundaryWeight parameters grade mode : ℂ)⁻¹ • value))) =
        lp.single 2 mode value := by
  classical
  apply Subtype.ext
  funext output
  rw [finiteBoundaryToGrade_apply]
  by_cases equal : output = mode
  · subst output
    simp only [Finsupp.single_eq_same, lp.single_apply_self]
    exact smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr (boundaryWeight_pos parameters grade mode).ne') value
  · rw [lp.single_apply_ne (E := fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode value equal]
    by_cases cellEqual : output.2 = mode.2
    · have modeNe : output.1 ≠ mode.1 := fun modeEqual => equal (Prod.ext modeEqual cellEqual)
      simp [cellEqual, modeNe]
    · simp [cellEqual]

theorem finiteBoundaryToGrade_dense {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) :
    DenseRange (finiteBoundaryToGrade (dimension := dimension) parameters grade gradePositive) := by
  classical
  intro field
  let image := LinearMap.range (finiteBoundaryToGrade (dimension := dimension) parameters grade gradePositive)
  change field ∈ image.topologicalClosure
  apply image.isClosed_topologicalClosure.mem_of_tendsto (lp.hasSum_single (by norm_num) field)
  apply Filter.Eventually.of_forall
  intro modes
  apply image.topologicalClosure.sum_mem
  intro mode _
  apply image.le_topologicalClosure
  exact ⟨Finsupp.single mode.2 (Finsupp.single mode.1
    ((boundaryWeight parameters grade mode : ℂ)⁻¹ • field mode)),
      finiteBoundaryToGrade_single parameters grade gradePositive mode (field mode)⟩

end Grad.BoundaryLift
