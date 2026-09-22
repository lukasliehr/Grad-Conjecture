import Q23CompletedTranspose
import GaugeProjectionBounds

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 2400000

open Filter
open scoped BigOperators Topology

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers Grad.Constraints.Gauges Grad.Constraints.Seed

/-- Fixed value maps on one completed original grade. -/
def q23ValueMapCompleted (phase : PhaseParameters) {source target grade : ℕ}
    (mapping : ComplexEuclidean source →L[ℂ] ComplexEuclidean target) :
    AGrade phase source grade →L[ℂ] AGrade phase target grade :=
  (valueMapGradeCoreContinuous mapping phase).completion

theorem q23ValueMapCompleted_core (phase : PhaseParameters)
    {source target grade : ℕ}
    (mapping : ComplexEuclidean source →L[ℂ] ComplexEuclidean target)
    (field : ACore phase source) :
    q23ValueMapCompleted (grade := grade) phase mapping
        (aGradeEta phase (GradeCore.ofCoreLinear (grade := grade) field)) =
      aGradeEta phase (GradeCore.ofCoreLinear (grade := grade)
        (valueMapCore mapping phase field)) := by
  rw [q23ValueMapCompleted, aGradeEta_apply,
    ContinuousLinearMap.completion_apply_coe]
  rfl

def coordinateGradeCoreToCompletion (phase : PhaseParameters) (grade : ℕ)
    (coordinate : Fin 2) :
    GradeCore phase 1 grade →ₗ[ℂ] AGrade phase 1 grade :=
  (aGradeEta phase).toLinearMap.comp
    (GradeCore.ofCoreLinear.comp
      ((coordinateCore phase coordinate).comp GradeCore.toCoreLinear))

theorem coordinateGradeCoreToCompletion_bound (phase : PhaseParameters)
    (grade : ℕ) (coordinate : Fin 2) (field : GradeCore phase 1 grade) :
    ‖coordinateGradeCoreToCompletion phase grade coordinate field‖ ≤
      coordinateRowConstant grade * ‖field‖ := by
  change ‖aGradeEta phase (GradeCore.ofCoreLinear
    (coordinateCore phase coordinate field.toCore))‖ ≤ _
  rw [aGradeEta_norm, gradeCore_norm_eq_cartesianGradeSeminorm,
    gradeCore_norm_eq_cartesianGradeSeminorm, cartesianGradeSeminorm_apply,
    cartesianGradeSeminorm_apply, gradeCoreCoordinates_apply, gradeCoreCoordinates_apply]
  exact coordinateCore_coordinates_bound phase coordinate field.toCore grade

/-- Multiplication by a fixed planar coordinate on the completed grade. -/
def coordinateCompleted (phase : PhaseParameters) (grade : ℕ)
    (coordinate : Fin 2) :
    AGrade phase 1 grade →L[ℂ] AGrade phase 1 grade :=
  (coordinateGradeCoreToCompletion phase grade coordinate).mkContinuous
      (coordinateRowConstant grade)
      (coordinateGradeCoreToCompletion_bound phase grade coordinate) |>.fromCompletion

theorem coordinateCompleted_core (phase : PhaseParameters) (grade : ℕ)
    (coordinate : Fin 2) (field : ACore phase 1) :
    coordinateCompleted phase grade coordinate
        (aGradeEta phase (GradeCore.ofCoreLinear (grade := grade) field)) =
      aGradeEta phase (GradeCore.ofCoreLinear (grade := grade)
        (coordinateCore phase coordinate field)) := by
  exact ContinuousLinearMap.fromCompletion_apply_coe _
    (GradeCore.ofCoreLinear (grade := grade) field)

def derivativeDotLeft (phase : PhaseParameters) (grade : ℕ)
    (coordinate : Fin 2) :
    AGrade phase 2 grade →L[ℂ] AGrade phase 1 grade :=
  (coordinateCompleted phase grade coordinate).comp
    (q23ValueMapCompleted phase (planarComponentMap coordinate))

/-- Fixed bounded linear postprocessing turning multiplication by `M'ᵀ` into
the literal dot `u · M' y`. -/
def derivativeDotLift (phase : PhaseParameters) (grade : ℕ) :
    (AGrade phase 2 grade →L[ℂ] AGrade phase 2 grade) →L[ℂ]
      (AGrade phase 2 grade →L[ℂ] AGrade phase 1 grade) :=
  (ContinuousLinearMap.compL ℂ (AGrade phase 2 grade) (AGrade phase 2 grade)
    (AGrade phase 1 grade)) (derivativeDotLeft phase grade 0) +
  (ContinuousLinearMap.compL ℂ (AGrade phase 2 grade) (AGrade phase 2 grade)
    (AGrade phase 1 grade)) (derivativeDotLeft phase grade 1)

theorem derivativeDotLift_norm_le (phase : PhaseParameters) (grade : ℕ)
    (mapping : AGrade phase 2 grade →L[ℂ] AGrade phase 2 grade) :
    ‖derivativeDotLift phase grade mapping‖ ≤
      (‖derivativeDotLeft phase grade 0‖ + ‖derivativeDotLeft phase grade 1‖) *
        ‖mapping‖ := by
  unfold derivativeDotLift
  simp only [add_apply, ContinuousLinearMap.compL_apply]
  calc
    ‖(derivativeDotLeft phase grade 0).comp mapping +
        (derivativeDotLeft phase grade 1).comp mapping‖
        ≤ ‖(derivativeDotLeft phase grade 0).comp mapping‖ +
            ‖(derivativeDotLeft phase grade 1).comp mapping‖ :=
      norm_add_le ((derivativeDotLeft phase grade 0).comp mapping)
        ((derivativeDotLeft phase grade 1).comp mapping)
    _ ≤ ‖derivativeDotLeft phase grade 0‖ * ‖mapping‖ +
          ‖derivativeDotLeft phase grade 1‖ * ‖mapping‖ :=
      add_le_add ((derivativeDotLeft phase grade 0).opNorm_comp_le mapping)
        ((derivativeDotLeft phase grade 1).opNorm_comp_le mapping)
    _ = _ := by ring

/-- Actual every-order finite-seed derivative of the completed `M'` dot
operator. -/
def completedDerivativeDotParameterDerivative (phase : PhaseParameters)
    (grade order : ℕ) (parameter : Seed.Parameters)
    (directions : Fin order → Seed.Parameters) :
    AGrade phase 2 grade →L[ℂ] AGrade phase 1 grade :=
  derivativeDotLift phase grade
    (completedSeedTransposeParameterDerivative phase grade order 2 parameter directions)

/-- The same every-order derivative on the accepted smooth coefficient core. -/
def seedDerivativeDotParameterDerivative (phase : PhaseParameters) (order : ℕ)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) :
    ACore phase 2 →ₗ[ℂ] ACore phase 1 :=
  (coordinateCore phase 0).comp
      ((valueMapCore (planarComponentMap 0) phase).comp
        (seedTransposeParameterMultiplier phase order 2 parameter inside directions)) +
    (coordinateCore phase 1).comp
      ((valueMapCore (planarComponentMap 1) phase).comp
        (seedTransposeParameterMultiplier phase order 2 parameter inside directions))

theorem valueMapCore_smoothMultiplier_comp
    {source middle target : ℕ} (phase : PhaseParameters)
    (mapping : ComplexEuclidean middle →L[ℂ] ComplexEuclidean target)
    (coefficients : ℤ → ComplexEuclidean source →L[ℂ] ComplexEuclidean middle)
    (summable : ∀ grade, Summable (envelopeTerm phase grade coefficients))
    (composedSummable : ∀ grade, Summable (envelopeTerm phase grade
      (fun cell => mapping.comp (coefficients cell))))
    (field : ACore phase source) :
    valueMapCore mapping phase (smoothMultiplier phase coefficients summable field) =
      smoothMultiplier phase (fun cell => mapping.comp (coefficients cell))
        composedSummable field := by
  apply Subtype.ext
  funext cell
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have mapped := mapping.hasSum
    (smoothMultiplier_value_hasSum phase coefficients summable field cell point)
  have composed := smoothMultiplier_value_hasSum phase
    (fun shift => mapping.comp (coefficients shift)) composedSummable field cell point
  rw [valueMapCore_apply, valueMapJet_value]
  change mapping (((smoothMultiplier phase coefficients summable field).1 cell).value point) =
    ((smoothMultiplier phase (fun shift => mapping.comp (coefficients shift))
      composedSummable field).1 cell).value point
  exact mapped.unique composed

theorem completedDerivativeDotParameterDerivative_core (phase : PhaseParameters)
    (grade order : ℕ) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) (field : ACore phase 2) :
    completedDerivativeDotParameterDerivative phase grade order parameter directions
        (aGradeEta phase (GradeCore.ofCoreLinear field)) =
      aGradeEta phase (GradeCore.ofCoreLinear
        (seedDerivativeDotParameterDerivative phase order parameter inside directions field)) := by
  unfold completedDerivativeDotParameterDerivative derivativeDotLift derivativeDotLeft
    seedDerivativeDotParameterDerivative
  simp only [add_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, LinearMap.add_apply, LinearMap.comp_apply]
  rw [completedSeedTransposeParameterDerivative_core phase grade order 2 parameter inside
      directions field,
    q23ValueMapCompleted_core, coordinateCompleted_core,
    q23ValueMapCompleted_core, coordinateCompleted_core, map_add]
  rw [← map_add]

theorem seedDerivativeDotParameterDerivative_zero (phase : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain) :
    seedDerivativeDotParameterDerivative phase 0 parameter inside
        (fun position => position.elim0) =
      derivativeDotCore phase parameter inside := by
  apply LinearMap.ext
  intro field
  unfold seedDerivativeDotParameterDerivative derivativeDotCore
  simp only [LinearMap.add_apply, LinearMap.comp_apply]
  rw [seedTransposeParameterMultiplier_zero phase 2 parameter inside field]
  congr 1
  · change (coordinateCore phase 0) ((valueMapCore (planarComponentMap 0) phase)
        ((smoothMultiplier phase
          (fun cell => transposeOperator (Seed.actualCells 2 parameter cell)) _) field)) =
      (coordinateCore phase 0) ((smoothMultiplier phase
        (fun cell => (planarComponentMap 0).comp
          (transposeOperator (Seed.actualCells 2 parameter cell))) _) field)
    exact congrArg (coordinateCore phase 0)
      (valueMapCore_smoothMultiplier_comp phase (planarComponentMap 0)
        (fun cell => transposeOperator (Seed.actualCells 2 parameter cell))
        (fun grade => transpose_envelope_summable phase grade _
          (seedCells_all_summable phase parameter inside 2 grade))
        (fun grade => derivativeRowCoefficients_envelope_summable phase parameter inside 0 grade)
        field)
  · change (coordinateCore phase 1) ((valueMapCore (planarComponentMap 1) phase)
        ((smoothMultiplier phase
          (fun cell => transposeOperator (Seed.actualCells 2 parameter cell)) _) field)) =
      (coordinateCore phase 1) ((smoothMultiplier phase
        (fun cell => (planarComponentMap 1).comp
          (transposeOperator (Seed.actualCells 2 parameter cell))) _) field)
    exact congrArg (coordinateCore phase 1)
      (valueMapCore_smoothMultiplier_comp phase (planarComponentMap 1)
        (fun cell => transposeOperator (Seed.actualCells 2 parameter cell))
        (fun grade => transpose_envelope_summable phase grade _
          (seedCells_all_summable phase parameter inside 2 grade))
        (fun grade => derivativeRowCoefficients_envelope_summable phase parameter inside 1 grade)
        field)

/-- The derivative-dot tower is a genuine operator-norm derivative tower in
the newest seed direction. -/
theorem completedDerivativeDotParameterDerivative_genuine (phase : PhaseParameters)
    (grade order : ℕ) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (oldDirections : Fin order → Seed.Parameters)
    (newDirection : Seed.Parameters) :
    Tendsto (fun t : ℝ =>
      ‖(((t : ℂ))⁻¹ •
          (completedDerivativeDotParameterDerivative phase grade order
              (parameter + t • newDirection) oldDirections -
            completedDerivativeDotParameterDerivative phase grade order
              parameter oldDirections)) -
        completedDerivativeDotParameterDerivative phase grade (order + 1) parameter
          (Fin.cons newDirection oldDirections)‖)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have sourceLimit := completedSeedTransposeParameterDerivative_genuine
    phase grade order 2 parameter inside oldDirections newDirection
  refine squeeze_zero' ?_
    (g := fun t : ℝ =>
      (‖derivativeDotLeft phase grade 0‖ + ‖derivativeDotLeft phase grade 1‖) *
      ‖(((t : ℂ))⁻¹ •
          (completedSeedTransposeParameterDerivative phase grade order 2
              (parameter + t • newDirection) oldDirections -
            completedSeedTransposeParameterDerivative phase grade order 2
              parameter oldDirections)) -
        completedSeedTransposeParameterDerivative phase grade (order + 1) 2 parameter
          (Fin.cons newDirection oldDirections)‖) ?_ ?_
  · apply Eventually.of_forall
    intro t
    positivity
  · apply Eventually.of_forall
    intro t
    simp only [completedDerivativeDotParameterDerivative]
    rw [← map_sub, ← map_smul, ← map_sub]
    exact derivativeDotLift_norm_le phase grade _
  · simpa only [mul_zero] using tendsto_const_nhds.mul sourceLimit

end Grad.NonlinearQuotientBounds
