import AKU24ActualCubicLiftAxisAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Algebra Grad.FlatSourceProjection

@[simp] theorem axisPhysicalValue_add {parameters : PhaseParameters} {dimension : ℕ}
    (first second : Grad.AxisCore.AxisSmoothCore parameters dimension) (angle : ℝ) :
    axisPhysicalValue (first+second) angle = axisPhysicalValue first angle + axisPhysicalValue second angle :=
  map_add (axisPhysicalEvaluation dimension angle) first second

@[simp] theorem axisPhysicalValue_sub {parameters : PhaseParameters} {dimension : ℕ}
    (first second : Grad.AxisCore.AxisSmoothCore parameters dimension) (angle : ℝ) :
    axisPhysicalValue (first-second) angle = axisPhysicalValue first angle - axisPhysicalValue second angle :=
  map_sub (axisPhysicalEvaluation dimension angle) first second

@[simp] theorem axisPhysicalValue_smul {parameters : PhaseParameters} {dimension : ℕ}
    (scalar : ℂ) (data : Grad.AxisCore.AxisSmoothCore parameters dimension) (angle : ℝ) :
    axisPhysicalValue (scalar • data) angle = scalar • axisPhysicalValue data angle :=
  map_smul (axisPhysicalEvaluation dimension angle) scalar data

@[simp] theorem axisPhysicalValue_neg {parameters : PhaseParameters} {dimension : ℕ}
    (data : Grad.AxisCore.AxisSmoothCore parameters dimension) (angle : ℝ) :
    axisPhysicalValue (-data) angle = -axisPhysicalValue data angle :=
  map_neg (axisPhysicalEvaluation dimension angle) data

theorem axisComponent_physical {parameters : PhaseParameters} {dimension : ℕ}
    (component : Fin dimension) (data : Grad.AxisCore.AxisSmoothCore parameters dimension) (angle : ℝ) :
    axisPhysicalValue (axisComponent component data) angle = componentValue dimension component (axisPhysicalValue data angle) :=
  axisValueMap_physical _ data angle

theorem scalarAxisPair_physical {parameters : PhaseParameters}
    (first second : Grad.AxisCore.AxisSmoothCore parameters 1) (angle : ℝ) :
    axisPhysicalValue (scalarAxisPair first second) angle =
      WithLp.toLp 2 ![axisPhysicalValue first angle 0,axisPhysicalValue second angle 0] := by
  rw [scalarAxisPair,axisPhysicalValue_add,axisValueMap_physical,axisValueMap_physical]
  apply PiLp.ext
  intro component
  fin_cases component <;> simp [scalarAxisPairFirst,scalarAxisPairSecond]

theorem axisCovectorTriple_physical {parameters : PhaseParameters}
    (planar : Grad.AxisCore.AxisSmoothCore parameters 2) (toroidal : Grad.AxisCore.AxisSmoothCore parameters 1) (angle : ℝ) :
    axisPhysicalValue (axisCovectorTriple planar toroidal) angle =
      axisCovectorValue (axisPhysicalValue planar angle) (axisPhysicalValue toroidal angle 0) := by
  rw [axisCovectorTriple,axisPhysicalValue_add,axisValueMap_physical,axisValueMap_physical]
  apply PiLp.ext
  intro component
  fin_cases component <;>
    simp [matrixOperator,firstTwoInclusion,firstTwoProjection,axisCovectorValue,matrixUnit_apply,operatorBasis,Fintype.sum_prod_type,Fin.sum_univ_three,Fin.sum_univ_two]

theorem axisQuadraticDivergence_physical {parameters : PhaseParameters}
    (data : PlanarQuadraticAxisData parameters) (angle : ℝ) :
    axisPhysicalValue (axisQuadraticDivergence data) angle =
      quadraticDivergenceCoefficients (fun index => axisPhysicalValue (data index) angle) := by
  rw [axisQuadraticDivergence,scalarAxisPair_physical]
  simp only [axisPhysicalValue_add,axisPhysicalValue_smul,axisComponent_physical]
  apply PiLp.ext
  intro component
  fin_cases component <;> simp [quadraticDivergenceCoefficients,componentValue_apply]

theorem axisCubicComplementVector_physical {parameters : PhaseParameters}
    (linear : Grad.AxisCore.AxisSmoothCore parameters 2) (angle : ℝ) (index : Fin 3) :
    axisPhysicalValue (axisCubicComplementVector linear index) angle =
      cubicComplementVectorCoefficients (axisPhysicalValue linear angle) index := by
  fin_cases index <;> simp [axisCubicComplementVector,scalarAxisPair_physical,axisPhysicalValue_smul,
    axisComponent_physical,componentValue_apply,cubicComplementVectorCoefficients]

theorem quadraticAxisPlanarOperator_physical {parameters : PhaseParameters}
    (data : PlanarQuadraticAxisData parameters) (angle : ℝ) (index : Fin 3) :
    axisPhysicalValue (quadraticAxisPlanarOperator data index) angle =
      quadraticPlanarOperator (fun slot => axisPhysicalValue (data slot) angle) index := by
  fin_cases index <;> simp [quadraticAxisPlanarOperator,quadraticPlanarOperator,
    quadraticRotation,quadraticQuarterTurn,axisValueMap_physical]

theorem quadraticAxisPlanarInverse_physical {parameters : PhaseParameters}
    (data : PlanarQuadraticAxisData parameters) (angle : ℝ) (index : Fin 3) :
    axisPhysicalValue (quadraticAxisPlanarInverse data index) angle =
      quadraticPlanarInverse (fun slot => axisPhysicalValue (data slot) angle) index := by
  change axisPhysicalValue (-(1/9 : ℂ) •
    (quadraticAxisPlanarOperator (quadraticAxisPlanarOperator (quadraticAxisPlanarOperator data)) index +
      (10 : ℂ) • quadraticAxisPlanarOperator data index)) angle = _
  simp only [axisPhysicalValue_smul,axisPhysicalValue_add,quadraticAxisPlanarOperator_physical]
  rfl

end Grad.FinitePhysicalJetLift
