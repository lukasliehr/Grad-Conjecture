import ANL10GradeCompatibility

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace Grad.CircularNormalLift
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.BoundaryLift Grad.Constraints
open Grad.CircularHighWeak Grad.OrdinaryDiskCalculus Grad.OrdinaryDiskFaithfulness Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.WeightedTrace
local instance (priority := 2000) smoothLiftUnitSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) := unitNormedSpace grade
local instance (priority := 2000) smoothLiftBoundarySpace (grade : ℕ) : NormedSpace ℂ (normalBoundaryGrade grade) :=
  (normalBoundaryGrade grade).normedSpace

def normalSmoothFamily (data : NormalSmoothBoundary) (grade : ℕ) : unitDiskSobolev grade :=
  unitLower (show grade ≤ grade + 2 by omega) (completedNormalLift (grade + 2) (data.grade grade))

theorem normalSmoothFamily_bulk (data : NormalSmoothBoundary) (grade : ℕ) :
    unitDiskBulk grade (normalSmoothFamily data grade) = normalSmoothBulk data :=
  (unitLower_bulk (show grade ≤ grade + 2 by omega) _).trans (completedNormalLift_same_bulk data grade)

/-- One genuine closed jet representing the completed normal lift at every grade. -/
def normalSmoothLift (parameters : PhaseParameters) (data : NormalSmoothBoundary) : ClosedJet 1 :=
  sameBulkClosedJet parameters (normalSmoothFamily data) (normalSmoothBulk data) (normalSmoothFamily_bulk data)

theorem normalSmoothLift_bulk (parameters : PhaseParameters) (data : NormalSmoothBoundary) :
    closedL2Core (normalSmoothLift parameters data) = normalSmoothBulk data :=
  sameBulkClosedJet_bulk parameters (normalSmoothFamily data) (normalSmoothBulk data) (normalSmoothFamily_bulk data)

theorem normalSmoothLift_core (parameters : PhaseParameters) (data : NormalSmoothBoundary) (order : ℕ) :
    unitDiskCoreInto (order + 2) (normalSmoothLift parameters data) =
      completedNormalLift (order + 2) (data.grade order) := by
  apply ordinaryBulk_injective parameters (order + 2)
  exact (unitDiskBulk_core (order + 2) (normalSmoothLift parameters data)).trans
    ((normalSmoothLift_bulk parameters data).trans (completedNormalLift_same_bulk data order).symm)

theorem normalSmoothLift_bound (parameters : PhaseParameters) (data : NormalSmoothBoundary) (order : ℕ) :
    ‖unitDiskCoreInto (order + 2) (normalSmoothLift parameters data)‖ ≤
      Real.sqrt (normalSobolevConstant (order + 2)) * ‖data.grade order‖ := by
  exact (congrArg norm (normalSmoothLift_core parameters data order)).le.trans
    (completedNormalLift_bound (order + 2) (by omega) (data.grade order))

theorem normalSmoothLift_value_trace (parameters : PhaseParameters) (data : NormalSmoothBoundary) (order : ℕ) :
    ordinaryBoundaryTrace (order + 2) (by omega)
      (unitDiskCoreInto (order + 2) (normalSmoothLift parameters data)) = 0 := by
  rw [normalSmoothLift_core]
  exact completedNormalLift_zero_trace (order + 2) (by omega) (data.grade order)

theorem normalSmoothLift_normal_trace (parameters : PhaseParameters) (data : NormalSmoothBoundary) (order : ℕ) :
    ordinaryNormalTrace order (unitDiskCoreInto (order + 2) (normalSmoothLift parameters data)) = (data.grade order).val := by
  rw [normalSmoothLift_core]
  exact completedNormalLift_normal_trace order (data.grade order)

theorem normalSmoothLift_normal_coefficient (parameters : PhaseParameters) (data : NormalSmoothBoundary)
    (order : ℕ) (mode : ℤ) :
    fourierCoeff (fun angle : CellCircle =>
      (eulerJet (normalSmoothLift parameters data)).value (boundaryDiskPoint angle)) mode =
        normalBoundaryCoefficient (order + 2) (data.grade order) mode := by
  have coefficient := congrArg (fun field => apBoundaryCoefficient 1 0 0 1 (order + 1) field (mode, 0))
    (normalSmoothLift_normal_trace parameters data order)
  rw [ordinaryNormalTrace_core_coefficient, if_pos rfl] at coefficient
  exact coefficient

theorem closedBoundary_zero_of_coefficients (core : ClosedJet 1)
    (zeroCoefficients : ∀ mode : ℤ,
      fourierCoeff (fun angle : CellCircle => core.value (boundaryDiskPoint angle)) mode = 0) :
    ∀ angle, core.value (boundaryDiskPoint angle) = 0 := by
  have fourierZero : diskBoundaryFourier (diskCoreInto core) = 0 := by
    apply lp.ext
    funext output
    by_cases cellZero : output.2 = 0
    · have same : output = (output.1, 0) := Prod.ext rfl cellZero
      rw [same, diskBoundaryFourier_core_cell, zeroCoefficients]
      rfl
    · rw [diskBoundaryFourier_core_zero core output.1 output.2 cellZero]
      rfl
  have boundarySquared : ‖coreBoundaryL2 core‖ ^ 2 = 0 := by
    rw [coreBoundaryL2_fourier_norm_sq, fourierZero, norm_zero, zero_pow (by decide), mul_zero]
  have boundaryZero : coreBoundaryL2 core = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp boundarySquared)
  have continuousZero : closedBoundaryValue core = 0 := by
    apply ContinuousMap.toLp_injective (p := 2) volume (𝕜 := ℂ)
    exact boundaryZero.trans (map_zero (ContinuousMap.toLp 2 volume ℂ)).symm
  intro angle
  exact congrArg (fun value : C(CellCircle, ComplexEuclidean 1) => value angle) continuousZero

/-- Literal zero boundary value, in addition to the completed trace identity. -/
theorem normalSmoothLift_boundary (parameters : PhaseParameters) (data : NormalSmoothBoundary) (angle : CellCircle) :
    (normalSmoothLift parameters data).value (boundaryDiskPoint angle) = 0 := by
  apply closedBoundary_zero_of_coefficients _ _ angle
  intro mode
  have coefficient := congrArg (fun field => apBoundaryCoefficient 1 0 0 1 2 field (mode, 0))
    (normalSmoothLift_value_trace parameters data 0)
  rw [ordinaryBoundaryTrace_core_coefficient, if_pos rfl] at coefficient
  exact coefficient.trans (smul_zero _)

end Grad.CircularNormalLift
