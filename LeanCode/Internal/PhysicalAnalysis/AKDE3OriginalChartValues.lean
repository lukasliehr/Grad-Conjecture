import AKDE2ConstructedRealFields
import QO16ChartNormalization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3500
open Set
open scoped ContDiff

namespace Grad.OriginalCellFamily
open Grad.CartesianState Grad.ClosedJets Grad.Constraints Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.OriginalParameterEvaluation Grad.AxisSplit Grad.GaugeCoefficients.Physical.Frame

variable {parameters : PhaseParameters}

/-- The existing coefficient algebra evaluates to the SAME original P09 disk value. -/
theorem originalExtendedField_coreValue {dimension : ℕ} (field : ACore parameters dimension)
    (point : ClosedDisk) (cell : ℝ) :
    originalExtendedField parameters field (assembleSpatialCell point.val cell) = coreValue field point cell := by
  rw [originalExtendedField_onDisk]
  change originalPhysicalEvaluationLift parameters (GradeCore.ofCoreLinear (grade := 0) field) point cell = _
  rw [originalPhysicalEvaluationLift_eq_tsum]
  apply tsum_congr
  intro index
  rw [show cellExponential index cell = axialPhase index cell from
    ((axialPhase_eq_character index cell).trans (cellCharacter_coe index cell)).symm]
  rfl

theorem realExtendedField_coreValue {dimension : ℕ} (field : ACore parameters dimension)
    (point : ClosedDisk) (cell : ℝ) :
    originalRealExtendedField parameters field (assembleSpatialCell point.val cell) =
      physicalRealPart dimension (coreValue field point cell) := by
  unfold originalRealExtendedField
  rw [originalExtendedField_coreValue]

theorem coreValue_tameCoordinate (coordinate : Fin 2) (point : ClosedDisk) (cell : ℝ) :
    coreValue (tameCoordinateScalarField parameters coordinate) point cell =
      point.val coordinate • EuclideanSpace.single 0 (1 : ℂ) := by
  rw [tameCoordinateScalarField,singleton_coordinate]
  exact (coreValue_coordinate coordinate _ point cell).trans
    (congrArg (fun value => point.val coordinate • value) (coreValue_constant _ point cell))

theorem coreValue_tamePlanarCoordinate (point : ClosedDisk) (cell : ℝ) :
    coreValue (tamePlanarCoordinateField parameters) point cell =
      physicalComplexification 2 point.val := by
  rw [tamePlanarCoordinateField,singleton_coordinate,singleton_coordinate,coreValue_add,
    coreValue_coordinate,coreValue_coordinate]
  change point.val 0 • coreValue (constantCore parameters (EuclideanSpace.single 0 1)) point cell +
    point.val 1 • coreValue (constantCore parameters (EuclideanSpace.single 1 1)) point cell = _
  rw [coreValue_constant,coreValue_constant]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [physicalComplexification]

theorem coreValue_tameSeed (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (point : ClosedDisk) (cell : ℝ) :
    coreValue (tameSeedField parameters seed inside) point cell =
      tamePlanarInclusion (harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3) cell
        (physicalComplexification 2 point.val)) := by
  rw [tameSeedField,coreValue_valueMap,tameSeedPlanarField,coreValue_seedMatrix,coreValue_tamePlanarCoordinate]

/-- Literal normalized chart values on the whole original disk. No spatial
extension identity outside the disk is needed for this formula. -/
theorem originalNormalizedChart_value (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (state : ChartState parameters) (point : ClosedDisk) (cell : ℝ) :
    originalExtendedField parameters (normalizedChart parameters seed inside state).1
        (assembleSpatialCell point.val cell) =
      coefficientValue (rootChart state.1) cell •
        tamePlanarInclusion (harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3) cell
          (physicalComplexification 2 point.val)) +
      tameTangentInclusion ((planarValue state.1 cell 0 * point.val 0 +
        planarValue state.1 cell 1 * point.val 1) • EuclideanSpace.single 0 1) +
      coreValue state.2.1 point cell := by
  rw [originalExtendedField_coreValue]
  change coreValue (tameScalarMultiplier 3 (rootChart state.1) (tameSeedField parameters seed inside) +
    valueMapCore parameters tameTangentInclusion
      (tameScalarMultiplier 1 (tangentComponent state.1 0) (tameCoordinateScalarField parameters 0) +
        tameScalarMultiplier 1 (tangentComponent state.1 1) (tameCoordinateScalarField parameters 1)) + state.2.1) point cell = _
  rw [coreValue_add,coreValue_add,coreValue_tameScalarMultiplier,coreValue_tameSeed,
    coreValue_valueMap,coreValue_add,coreValue_tameScalarMultiplier,coreValue_tameScalarMultiplier,
    coreValue_tameCoordinate,coreValue_tameCoordinate,← planarValue_apply,← planarValue_apply]
  have same : planarValue state.1 cell 0 • (point.val 0 • EuclideanSpace.single (0 : Fin 1) (1 : ℂ)) +
      planarValue state.1 cell 1 • (point.val 1 • EuclideanSpace.single (0 : Fin 1) (1 : ℂ)) =
      (planarValue state.1 cell 0 * point.val 0 + planarValue state.1 cell 1 * point.val 1) •
        EuclideanSpace.single (0 : Fin 1) (1 : ℂ) := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate
    simp
  rw [same]

end Grad.OriginalCellFamily
