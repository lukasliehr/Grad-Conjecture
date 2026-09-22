import AKU19AxisFiniteValueMaps
import AKU11ActualToroidalQuadraticCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.FlatSourceProjection Grad.QuotientProjection

abbrev PlanarQuadraticAxisData (parameters : PhaseParameters) := Fin 3 → Grad.AxisCore.AxisSmoothCore parameters 2

def quadraticAxisPlanarOperator {parameters : PhaseParameters} (data : PlanarQuadraticAxisData parameters) :
    PlanarQuadraticAxisData parameters :=
  ![data 1,(2 : ℂ) • data 2 - (2 : ℂ) • data 0,-data 1] + fun index => axisValueMap quarterValueMap (data index)

def quadraticAxisPlanarInverse {parameters : PhaseParameters} (data : PlanarQuadraticAxisData parameters) :
    PlanarQuadraticAxisData parameters :=
  -(1/9 : ℂ) • (quadraticAxisPlanarOperator (quadraticAxisPlanarOperator (quadraticAxisPlanarOperator data)) +
    (10 : ℂ) • quadraticAxisPlanarOperator data)

theorem quadraticAxisPlanarOperator_val {parameters : PhaseParameters} (data : PlanarQuadraticAxisData parameters)
    (cell : ℤ) (index : Fin 3) :
    (quadraticAxisPlanarOperator data index).val cell =
      quadraticPlanarOperator (fun slot => (data slot).val cell) index := by
  fin_cases index <;> rfl

theorem quadraticAxisPlanarInverse_val {parameters : PhaseParameters} (data : PlanarQuadraticAxisData parameters)
    (cell : ℤ) (index : Fin 3) :
    (quadraticAxisPlanarInverse data index).val cell =
      quadraticPlanarInverse (fun slot => (data slot).val cell) index := by
  fin_cases index <;> rfl

/-- The same six-dimensional finite inverse now acts on actual original
all-grade smooth axis coefficients. -/
theorem quadraticAxisPlanarOperator_inverse {parameters : PhaseParameters} (data : PlanarQuadraticAxisData parameters) :
    quadraticAxisPlanarOperator (quadraticAxisPlanarInverse data) = data := by
  funext index
  apply Subtype.ext
  funext cell
  rw [quadraticAxisPlanarOperator_val]
  have values : (fun slot => (quadraticAxisPlanarInverse data slot).val cell) =
      quadraticPlanarInverse (fun slot => (data slot).val cell) :=
    funext (quadraticAxisPlanarInverse_val data cell)
  rw [values,quadraticPlanarOperator_inverse]

def originalForce2Axis {parameters : PhaseParameters} (source : SmoothQuotient parameters) :
    PlanarQuadraticAxisData parameters :=
  ![(1/2 : ℂ) • traceFirst 0 (partialCore parameters 0 (cartesianSourceVector source)),
    traceFirst 0 (partialCore parameters 1 (cartesianSourceVector source)),
    (1/2 : ℂ) • traceFirst 1 (partialCore parameters 1 (cartesianSourceVector source))]

def scalarAxisPairFirst : ComplexEuclidean 1 →L[ℂ] ComplexEuclidean 2 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun value => WithLp.toLp 2 ![value 0,0]
      map_add' := by intros; apply PiLp.ext; intro index; fin_cases index <;> simp
      map_smul' := by intros; apply PiLp.ext; intro index; fin_cases index <;> simp }

def scalarAxisPairSecond : ComplexEuclidean 1 →L[ℂ] ComplexEuclidean 2 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun value => WithLp.toLp 2 ![0,value 0]
      map_add' := by intros; apply PiLp.ext; intro index; fin_cases index <;> simp
      map_smul' := by intros; apply PiLp.ext; intro index; fin_cases index <;> simp }

def scalarAxisPair {parameters : PhaseParameters} (first second : Grad.AxisCore.AxisSmoothCore parameters 1) :
    Grad.AxisCore.AxisSmoothCore parameters 2 :=
  axisValueMap scalarAxisPairFirst first + axisValueMap scalarAxisPairSecond second

theorem scalarAxisPair_val {parameters : PhaseParameters} (first second : Grad.AxisCore.AxisSmoothCore parameters 1)
    (cell : ℤ) : (scalarAxisPair first second).val cell = WithLp.toLp 2 ![first.val cell 0,second.val cell 0] := by
  apply PiLp.ext
  intro index
  fin_cases index <;> simp [scalarAxisPair,axisValueMap_val,scalarAxisPairFirst,scalarAxisPairSecond]

/-- Actual degree-one determinant source, with both Cartesian derivatives. -/
def originalG1Axis {parameters : PhaseParameters} (source : SmoothQuotient parameters) :
    Grad.AxisCore.AxisSmoothCore parameters 2 := scalarAxisPair (traceFirst 0 (source 2)) (traceFirst 1 (source 2))

def originalC2Axis {parameters : PhaseParameters} (length : ℝ) (source : SmoothQuotient parameters) :
    ScalarQuadraticAxisData parameters :=
  (length : ℂ)⁻¹ • ![-(1/4 : ℂ) • originalToroidalTargetAxis source 1,
    originalToroidalTargetAxis source 0,(1/4 : ℂ) • originalToroidalTargetAxis source 1]

theorem originalC2Axis_val {parameters : PhaseParameters} (length : ℝ) (source : SmoothQuotient parameters)
    (cell : ℤ) (index : Fin 3) :
    (originalC2Axis length source index).val cell 0 =
      scalarToroidalLiftCoefficients length ((cell : ℂ)*Complex.I)
        (originalScalarSourceJetCoefficients source cell) (scalarSecondTaylorCoefficients ((source 3).val cell)) index := by
  have target (slot : Fin 3) : (originalToroidalTargetAxis source slot).val cell 0 =
      scalarSecondTaylorCoefficients ((source 3).val cell) slot +
        ((cell : ℂ) * Complex.I) * originalScalarSourceJetCoefficients source cell slot := by
    change (scalarSecondTaylorAxis (source 3) slot).val cell 0 +
      (originalScalarHessianAxis (timeDifferentiatedSource source) slot).val cell 0 = _
    rw [scalarSecondTaylorAxis_val,originalScalarHessianAxis_time,originalScalarHessianAxis_val]
  fin_cases index
  all_goals simp [originalC2Axis,scalarToroidalLiftCoefficients,quadraticScalarAngularInverse]
  all_goals first | tauto | rfl | (rw [target]; ring)

end Grad.FinitePhysicalJetLift
