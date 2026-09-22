import ANL9OrdinaryNormalTrace

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace Grad.CircularNormalLift
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.BoundaryLift Grad.Constraints
open Grad.CircularHighWeak Grad.OrdinaryDiskCalculus
local instance (priority := 2000) compatUnitSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) := unitNormedSpace grade
local instance (priority := 2000) compatBoundarySpace (grade : ℕ) : NormedSpace ℂ (normalBoundaryGrade grade) :=
  (normalBoundaryGrade grade).normedSpace
local instance compatBoundaryComplete (grade : ℕ) : CompleteSpace (normalBoundaryGrade grade) := by
  unfold normalBoundaryGrade
  infer_instance

theorem normalBoundaryInto_lower_bound (low high : ℕ) (lowBound : 2 ≤ low) (ordered : low ≤ high)
    (values : NormalFiniteData) : ‖normalBoundaryInto low values‖ ≤ ‖normalBoundaryInto high values‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [normalBoundaryInto_norm_sq low lowBound, normalBoundaryInto_norm_sq high (lowBound.trans ordered)]
  apply Finset.sum_le_sum
  intro mode _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact pow_le_pow_right₀ (boundaryFrequency_one_le (mode, 0)) (by omega)

def normalBoundaryLower (low high : ℕ) : normalBoundaryGrade high →L[ℂ] normalBoundaryGrade low :=
  (normalBoundaryInto low).extendOfNorm (normalBoundaryInto high)

theorem normalBoundaryLower_finite (low high : ℕ) (lowBound : 2 ≤ low) (ordered : low ≤ high)
    (values : NormalFiniteData) :
    normalBoundaryLower low high (normalBoundaryInto high values) = normalBoundaryInto low values :=
  LinearMap.extendOfNorm_eq (normalBoundaryInto_denseRange high)
    ⟨1, fun values => (normalBoundaryInto_lower_bound low high lowBound ordered values).trans_eq (one_mul _).symm⟩ values

def normalBoundaryCoefficientCLM (grade : ℕ) (mode : ℤ) : normalBoundaryGrade grade →L[ℂ] ComplexEuclidean 1 :=
  ((normalBoundaryWeight grade mode : ℂ)⁻¹) •
    ((lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 (mode, 0)).comp (normalBoundaryGrade grade).subtypeL)

theorem normalBoundaryCoefficientCLM_apply (grade : ℕ) (mode : ℤ) (field : normalBoundaryGrade grade) :
    normalBoundaryCoefficientCLM grade mode field = normalBoundaryCoefficient grade field mode := rfl

theorem normalBoundaryLower_coefficient (low high : ℕ) (lowBound : 2 ≤ low) (ordered : low ≤ high)
    (field : normalBoundaryGrade high) (mode : ℤ) :
    normalBoundaryCoefficient low (normalBoundaryLower low high field) mode = normalBoundaryCoefficient high field mode := by
  apply isClosed_property (normalBoundaryInto_denseRange high)
    (isClosed_eq ((normalBoundaryCoefficientCLM low mode).continuous.comp (normalBoundaryLower low high).continuous)
      (normalBoundaryCoefficientCLM high mode).continuous) _ field
  intro values
  change normalBoundaryCoefficient low (normalBoundaryLower low high (normalBoundaryInto high values)) mode =
    normalBoundaryCoefficient high (normalBoundaryInto high values) mode
  rw [normalBoundaryLower_finite low high lowBound ordered, normalBoundaryInto_coefficient, normalBoundaryInto_coefficient]

theorem completedNormalLift_lower (low high : ℕ) (lowBound : 2 ≤ low) (ordered : low ≤ high)
    (field : normalBoundaryGrade high) :
    unitLower ordered (completedNormalLift high field) =
      completedNormalLift low (normalBoundaryLower low high field) := by
  apply isClosed_property (normalBoundaryInto_denseRange high)
    (isClosed_eq ((unitLower ordered).continuous.comp (completedNormalLift high).continuous)
      ((completedNormalLift low).continuous.comp (normalBoundaryLower low high).continuous)) _ field
  intro values
  dsimp only [Function.comp_apply]
  have upper := congrArg (fun field : unitDiskSobolev high => unitLower ordered field)
    (completedNormalLift_finite high (lowBound.trans ordered) values)
  have lower := completedNormalLift_finite low lowBound values
  have boundary := congrArg (fun field : normalBoundaryGrade low => completedNormalLift low field)
    (normalBoundaryLower_finite low high lowBound ordered values)
  exact upper.trans ((unitLower_core ordered (finiteNormalLinear values)).trans (lower.symm.trans boundary.symm))

/-- A smooth boundary datum in the exact compatible, completed circle grades. -/
structure NormalSmoothBoundary where
  grade : (order : ℕ) → normalBoundaryGrade (order + 2)
  coherent : ∀ order, normalBoundaryLower 2 (order + 2) (grade order) = grade 0

theorem smoothBoundary_coefficient (data : NormalSmoothBoundary) (order : ℕ) (mode : ℤ) :
    normalBoundaryCoefficient (order + 2) (data.grade order) mode =
      normalBoundaryCoefficient 2 (data.grade 0) mode := by
  rw [← normalBoundaryLower_coefficient 2 (order + 2) (by omega) (by omega), data.coherent order]

def normalSmoothBulk (data : NormalSmoothBoundary) : DiskL2 1 :=
  unitDiskBulk 2 (completedNormalLift 2 (data.grade 0))

theorem completedNormalLift_same_bulk (data : NormalSmoothBoundary) (order : ℕ) :
    unitDiskBulk (order + 2) (completedNormalLift (order + 2) (data.grade order)) = normalSmoothBulk data := by
  have lowered := completedNormalLift_lower 2 (order + 2) (by omega) (by omega) (data.grade order)
  have aligned := lowered.trans (congrArg (fun field : normalBoundaryGrade 2 => completedNormalLift 2 field) (data.coherent order))
  exact (unitLower_bulk (show 2 ≤ order + 2 by omega) _).symm.trans (congrArg (unitDiskBulk 2) aligned)

end Grad.CircularNormalLift
