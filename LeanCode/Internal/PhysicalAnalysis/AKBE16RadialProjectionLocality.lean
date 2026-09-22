import AKBE15RadialTestLocalization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.ActualCartesianWeakEquations
open Grad.PDEBootstrap Grad.ClosedJets Grad.Constraints Grad.PhysicalFamily Grad.CartesianStartup
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.RadialLedger

theorem closedCharacterProjection_norm_locality {dimension : ℕ} (mode : ℤ)
    (first second : ClosedDisk → ComplexEuclidean dimension) (point : ClosedDisk)
    (same : ∀ other : ClosedDisk, ‖other.val‖ = ‖point.val‖ → first other = second other) :
    closedCharacterProjection mode first point = closedCharacterProjection mode second point := by
  unfold closedCharacterProjection angularProjectionValue
  congr 1
  apply intervalIntegral.integral_congr
  intro angle _
  apply congrArg (fun value => angularCharacter mode angle • value)
  have equal := same (Grad.GaugeCoefficients.Radial.rotatedPoint angle point)
    (LinearIsometryEquiv.norm_map (planeRotationEquiv angle) point.val)
  have firstAt := closedFieldExtension_value first (Grad.GaugeCoefficients.Radial.rotatedPoint angle point)
  have secondAt := closedFieldExtension_value second (Grad.GaugeCoefficients.Radial.rotatedPoint angle point)
  have extensionSame := firstAt.trans (equal.trans secondAt.symm)
  simpa only [physicalRotation_eq_orthogonal,planeRotationEquiv_apply,Grad.GaugeCoefficients.Radial.rotatedPoint] using extensionSame

theorem closedEquivariantValue_norm_locality (first second : ClosedDisk → ComplexEuclidean 2)
    (point : ClosedDisk)
    (same : ∀ other : ClosedDisk, ‖other.val‖ = ‖point.val‖ → first other = second other) :
    closedEquivariantValue first point = closedEquivariantValue second point := by
  rw [closedEquivariantValue,closedEquivariantValue,
    closedCharacterProjection_norm_locality 1 first second point same,
    closedCharacterProjection_norm_locality (-1) first second point same]

/-- The literal original projector only uses values on the same circle. -/
theorem closedRadialReflectionValue_norm_locality (first second : ClosedDisk → ComplexEuclidean 2)
    (point : ClosedDisk)
    (same : ∀ other : ClosedDisk, ‖other.val‖ = ‖point.val‖ → first other = second other) :
    closedRadialReflectionValue first point = closedRadialReflectionValue second point := by
  have reflected : ∀ other : ClosedDisk,
      ‖other.val‖ = ‖(orthogonalClosedPoint cartesianReflectionEquiv point).val‖ → first other = second other := by
    intro other normSame
    apply same other
    exact normSame.trans (LinearIsometryEquiv.norm_map cartesianReflectionEquiv point.val)
  unfold closedRadialReflectionValue
  rw [same point rfl,closedEquivariantValue_norm_locality first second point same,
    closedEquivariantValue_norm_locality first second _ reflected]

/-- A nonzero projected test lies on the circle of an original support
point; both angular averaging and reflection preserve that radius. -/
theorem originalRawQradTest_nonzero_support (source target : Fin 2) (test : Spatial → ℝ)
    (point : Spatial) (nonzero : startupRawQradTest source test target point ≠ 0) :
    ∃ other ∈ tsupport test, ‖other‖ = ‖point‖ := by
  classical
  by_contra absent
  have vanishes (other : Spatial) (sameNorm : ‖other‖ = ‖point‖) : test other = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro membership
    exact absent ⟨other,membership,sameNorm⟩
  have average : startupAngularTest (fun angle => startupInverseRotationEntry source target (-angle)) test point = 0 := by
    unfold startupAngularTest
    simp only [vanishes _ (LinearIsometryEquiv.norm_map _ _),mul_zero,integral_zero,mul_zero]
  have reflected : startupAngularTest (fun angle => startupInverseRotationEntry source target (-angle))
      (fun query => test (cartesianReflectionEquiv query)) point = 0 := by
    unfold startupAngularTest
    have zero (angle : ℝ) : test (cartesianReflectionEquiv (planeRotationEquiv (-angle) point)) = 0 :=
      vanishes _ ((LinearIsometryEquiv.norm_map _ _).trans (LinearIsometryEquiv.norm_map _ _))
    simp only [zero,mul_zero,integral_zero,mul_zero]
  apply nonzero
  simp only [startupRawQradTest,vanishes point rfl,average,reflected,mul_zero,zero_add,sub_zero]

end Grad.ActualCartesianWeakEquations
