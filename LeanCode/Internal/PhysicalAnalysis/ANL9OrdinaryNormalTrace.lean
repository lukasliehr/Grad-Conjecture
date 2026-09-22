import ANL8CompletedNormalLift

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open Set MeasureTheory
open scoped BigOperators
namespace Grad.CircularNormalLift
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.BoundaryLift Grad.Constraints
open Grad.CircularHighWeak Grad.OrdinaryDiskCalculus Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.GaugeCoefficients.Physical.Compensated (partialJetLinear)
local instance (priority := 2000) traceUnitSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) :=
  unitNormedSpace grade
local instance (priority := 2000) traceBoundarySpace (grade : ℕ) : NormedSpace ℂ (normalBoundaryGrade grade) :=
  (normalBoundaryGrade grade).normedSpace

def eulerJetLinear : ClosedJet 1 →ₗ[ℂ] ClosedJet 1 :=
  (coordinateJetLinear 0).comp (partialJetLinear 1 0) + (coordinateJetLinear 1).comp (partialJetLinear 1 1)

theorem eulerJetLinear_apply (field : ClosedJet 1) : eulerJetLinear field = eulerJet field := rfl

theorem unitEuler_bound (grade : ℕ) (field : ClosedJet 1) :
    ‖unitSobolevRow grade (eulerJet field)‖ ≤ unitRotationConstant grade * ‖unitSobolevRow (grade + 1) field‖ := by
  have addition := (unitSobolevRow grade).map_add (coordinateJet 0 (partialJet 0 field)) (coordinateJet 1 (partialJet 1 field))
  have first := (unitCoordinate_bound grade 0 (partialJet 0 field)).trans
    (mul_le_mul_of_nonneg_left (unitPartial_bound grade 0 field) (unitCoordinateConstant_nonnegative grade 0))
  have second := (unitCoordinate_bound grade 1 (partialJet 1 field)).trans
    (mul_le_mul_of_nonneg_left (unitPartial_bound grade 1 field) (unitCoordinateConstant_nonnegative grade 1))
  exact (congrArg norm addition).le.trans ((norm_add_le _ _).trans ((add_le_add first second).trans_eq (by
    change _ = ((unitCoordinateConstant grade 0 + unitCoordinateConstant grade 1) * _) * _
    ring)))

def ordinaryEuler (grade : ℕ) : unitDiskSobolev (grade + 1) →L[ℂ] unitDiskSobolev grade :=
  Classical.choose (unitCore_extension (grade + 1) grade eulerJetLinear (unitRotationConstant grade)
    (unitRotationConstant_nonnegative grade) (unitEuler_bound grade))

theorem ordinaryEuler_core (grade : ℕ) (core : ClosedJet 1) :
    ordinaryEuler grade (unitDiskCoreInto (grade + 1) core) = unitDiskCoreInto grade (eulerJet core) :=
  (Classical.choose_spec (unitCore_extension (grade + 1) grade eulerJetLinear (unitRotationConstant grade)
    (unitRotationConstant_nonnegative grade) (unitEuler_bound grade))).1 core

def ordinaryBoundaryTrace (grade : ℕ) (positive : 1 ≤ grade) :
    unitDiskSobolev grade →L[ℂ] APBoundaryGrade 1 0 0 1 1 grade :=
  (apBoundaryTrace 1 0 0 1 grade positive).comp (unitDiskSobolev grade).subtypeL

theorem ordinaryBoundaryTrace_core_coefficient (grade : ℕ) (positive : 1 ≤ grade)
    (core : ClosedJet 1) (output : ℤ × ℤ) :
    apBoundaryCoefficient 1 0 0 1 grade (ordinaryBoundaryTrace grade positive (unitDiskCoreInto grade core)) output =
      if output.2 = 0 then fourierCoeff (fun angle : CellCircle => core.value (boundaryDiskPoint angle)) output.1 else 0 := by
  change apBoundaryCoefficient 1 0 0 1 grade
    (apBoundaryTrace 1 0 0 1 grade positive (Grad.GaugeCoefficients.Physical.RadialLedger.apFiniteInto 1 0 0 1 (Finsupp.single 0 core))) output = _
  rw [apBoundaryTrace_core, apCoreTraceLinear_coefficient, apCoreBoundaryCoefficient]
  by_cases cellZero : output.2 = 0
  · simp only [cellZero, Finsupp.single_eq_same, ite_true]
  · rw [Finsupp.single_eq_of_ne cellZero, if_neg cellZero]
    simp [fourierCoeff]

/-- Completed outward normal trace; Euler differentiation is normal at the unit circle. -/
def ordinaryNormalTrace (order : ℕ) :
    unitDiskSobolev (order + 2) →L[ℂ] APBoundaryGrade 1 0 0 1 1 (order + 1) :=
  (ordinaryBoundaryTrace (order + 1) (by omega)).comp (ordinaryEuler (order + 1))

theorem ordinaryNormalTrace_core_coefficient (order : ℕ) (core : ClosedJet 1) (output : ℤ × ℤ) :
    apBoundaryCoefficient 1 0 0 1 (order + 1)
      (ordinaryNormalTrace order (unitDiskCoreInto (order + 2) core)) output =
        if output.2 = 0 then fourierCoeff (fun angle : CellCircle =>
          (eulerJet core).value (boundaryDiskPoint angle)) output.1 else 0 := by
  rw [ordinaryNormalTrace, ContinuousLinearMap.comp_apply, ordinaryEuler_core]
  exact ordinaryBoundaryTrace_core_coefficient (order + 1) (by omega) (eulerJet core) output

theorem normalBoundaryInto_all_coefficient (grade : ℕ) (values : NormalFiniteData) (output : ℤ × ℤ) :
    apBoundaryCoefficient 1 0 0 1 (grade - 1) (normalBoundaryInto grade values).val output =
      if output.2 = 0 then values output.1 else 0 := by
  by_cases cellZero : output.2 = 0
  · have same : output = (output.1, 0) := Prod.ext rfl cellZero
    rw [same, if_pos rfl]
    exact normalBoundaryInto_coefficient grade values output.1
  · change ((apBoundaryWeight 1 0 0 1 (grade - 1) output : ℂ)⁻¹) •
      (if output.2 = 0 then (normalBoundaryWeight grade output.1 : ℂ) • values output.1 else 0) = _
    simp only [if_neg cellZero, smul_zero]

theorem completedNormalLift_zero_trace (grade : ℕ) (gradeBound : 2 ≤ grade)
    (field : normalBoundaryGrade grade) :
    ordinaryBoundaryTrace grade (by omega) (completedNormalLift grade field) = 0 := by
  apply isClosed_property (normalBoundaryInto_denseRange grade)
    (isClosed_eq ((ordinaryBoundaryTrace grade (by omega)).continuous.comp (completedNormalLift grade).continuous)
      continuous_const) _ field
  intro values
  dsimp only [Function.comp_apply]
  rw [completedNormalLift_finite grade gradeBound, finiteNormalLinear_eq]
  apply lp.ext
  funext output
  rw [← apBoundary_weighted_coefficient 1 0 0 1 grade _ output,
    ordinaryBoundaryTrace_core_coefficient]
  simp [finiteNormalJet_boundary, fourierCoeff]

private theorem boundary_coefficient_ext (grade : ℕ)
    (first second : APBoundaryGrade 1 0 0 1 1 grade)
    (same : ∀ output, apBoundaryCoefficient 1 0 0 1 grade first output =
      apBoundaryCoefficient 1 0 0 1 grade second output) : first = second := by
  apply lp.ext
  funext output
  exact (apBoundary_weighted_coefficient 1 0 0 1 grade first output).symm.trans
    ((congrArg (fun value : ComplexEuclidean 1 => (apBoundaryWeight 1 0 0 1 grade output : ℂ) • value)
      (same output)).trans (apBoundary_weighted_coefficient 1 0 0 1 grade second output))

theorem completedNormalLift_normal_trace (order : ℕ) (field : normalBoundaryGrade (order + 2)) :
    ordinaryNormalTrace order (completedNormalLift (order + 2) field) = field.val := by
  apply isClosed_property (normalBoundaryInto_denseRange (order + 2))
    (isClosed_eq ((ordinaryNormalTrace order).continuous.comp (completedNormalLift (order + 2)).continuous)
      (normalBoundaryGrade (order + 2)).subtypeL.continuous) _ field
  intro values
  dsimp only [Function.comp_apply]
  rw [completedNormalLift_finite (order + 2) (by omega), finiteNormalLinear_eq]
  apply boundary_coefficient_ext (order + 1)
  intro output
  rw [ordinaryNormalTrace_core_coefficient, finiteNormalJet_normal_coefficient]
  change (if output.2 = 0 then if output.1 ∈ values.support then values output.1 else 0 else 0) =
    apBoundaryCoefficient 1 0 0 1 (order + 2 - 1) (normalBoundaryInto (order + 2) values).val output
  rw [normalBoundaryInto_all_coefficient]
  by_cases member : output.1 ∈ values.support
  · rw [if_pos member]
  · rw [if_neg member, Finsupp.notMem_support_iff.mp member]

end Grad.CircularNormalLift
