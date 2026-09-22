import AKDE3OriginalChartValues
import RealComplexification

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxRecDepth 3500
open Set
open scoped ContDiff BigOperators

namespace Grad.OriginalCellFamily
open Grad.CartesianState Grad.ClosedJets Grad.Constraints Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.OriginalParameterEvaluation Grad.AxisSplit Grad.GaugeCoefficients.Physical.Frame
open Grad.PhysicalFamily Grad.MainTarget

variable {parameters : PhaseParameters}

theorem physicalComplexification_norm_sq (dimension : ℕ) (value : EuclideanSpace ℝ (Fin dimension)) :
    ‖physicalComplexification dimension value‖ ^ 2 = ‖value‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro coordinate _
  change ‖((value coordinate : ℝ) : ℂ)‖ ^ 2 = ‖value coordinate‖ ^ 2
  rw [Complex.norm_real,Real.norm_eq_abs]

def originalRealTilt (family : TangentCoefficient parameters) (cell : ℝ) : Plane :=
  physicalRealPart 2 (planarValue family cell)

theorem originalRealTilt_complexification (family : TangentCoefficient parameters)
    (real : RealTangent family) (cell : ℝ) :
    physicalComplexification 2 (originalRealTilt family cell) = planarValue family cell := by
  apply physicalComplexification_realPart
  apply PiLp.ext
  intro coordinate
  exact planarValue_conj real cell coordinate

theorem originalRealTilt_norm_sq (family : TangentCoefficient parameters)
    (real : RealTangent family) (cell : ℝ) :
    ‖originalRealTilt family cell‖ ^ 2 = ‖planarValue family cell‖ ^ 2 := by
  rw [← originalRealTilt_complexification family real cell,physicalComplexification_norm_sq]

theorem originalRealTilt_bound (family : TangentCoefficient parameters)
    (real : RealTangent family) (axis : RootAxisCondition family) (cell : ℝ) :
    ‖originalRealTilt family cell‖ ^ 2 < 2 := by
  rw [originalRealTilt_norm_sq family real cell]
  have small := rootAxis_planarValue_lt axis cell
  linarith

theorem originalRealTilt_root (family : TangentCoefficient parameters)
    (real : RealTangent family) (axis : RootAxisCondition family) (cell : ℝ) :
    coefficientValue (rootChart family) cell = (normalizedFactor (originalRealTilt family cell) : ℂ) := by
  rw [rootChart_value_eq_sqrt real axis]
  unfold normalizedFactor
  rw [originalRealTilt_norm_sq family real cell]

theorem realPart_planarInclusion (value : ComplexEuclidean 2) :
    physicalRealPart 3 (tamePlanarInclusion value) = planeEmbedding (physicalRealPart 2 value) := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> rfl

theorem harmonicSeedOperator_complexification (rho alpha delta parameter cell : ℝ) (point : Plane) :
    harmonicSeedOperator rho alpha delta parameter cell (physicalComplexification 2 point) =
      physicalComplexification 2 (seedAction rho alpha delta parameter cell point) := by
  apply PiLp.ext
  intro coordinate
  unfold harmonicSeedOperator
  rw [Grad.GaugeCoefficients.Physical.matrixEmbedding_apply]
  simp [physicalComplexification,seedAction,Matrix.mulVec,Fin.sum_univ_two,mul_comm]

/-- Real chart normalization is the literal positive square root and the
literal harmonic seed, with the actual original core remainder. -/
theorem originalRealNormalizedChart_value (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (state : ChartState parameters) (real : RealTangent state.1) (axis : ChartAxisCondition state)
    (point : Grad.ClosedJets.ClosedDisk) (cell : ℝ) :
    originalRealExtendedField parameters (normalizedChart parameters seed inside state).1
        (assembleSpatialCell point.val cell) =
      normalizedFactor (originalRealTilt state.1 cell) •
        planeEmbedding (seedAction (seed 0) (seed 1) (seed 2) (seed 3) cell point.val) +
      planeDot (originalRealTilt state.1 cell) point.val • tangentDirection +
      originalRealExtendedField parameters state.2.1 (assembleSpatialCell point.val cell) := by
  unfold originalRealExtendedField
  rw [originalNormalizedChart_value,originalExtendedField_coreValue,originalRealTilt_root state.1 real axis cell,
    harmonicSeedOperator_complexification]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [physicalRealPart,physicalComplexification,tamePlanarInclusion,tameTangentInclusion,
      planeEmbedding,planeDot,tangentDirection,originalRealTilt,vector,basisVector,Fin.sum_univ_two]

end Grad.OriginalCellFamily
