import AKU25VectorAxisProfileCore
import AKU24ActualCubicLiftAxisAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.FlatSourceProjection Grad.QuotientProjection Grad.GaugeCoefficients.Physical.Ledger
open Grad.NonlinearDivision Grad.GaugeCoefficients.Physical.Allocation

/-- A fixed genuine Cartesian monomial with a finite vector coefficient. -/
def coordinatePairConstantLinear (dimension : ℕ) (first second : Fin 2) :
    ComplexEuclidean dimension →ₗ[ℂ] ClosedJet dimension where
  toFun value := coordinateJet first (coordinateJet second (constantValueJet value))
  map_add' left right := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    simp only [coordinateJet_value,constantValueJet_value,closedJet_value_add,ContinuousMap.add_apply,smul_add]
  map_smul' scalar value := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    change (coordinateJet first (coordinateJet second (constantValueJet (scalar • value)))).value point =
      (scalar • coordinateJet first (coordinateJet second (constantValueJet value))).value point
    simp only [coordinateJet_value,constantValueJet_value,closedJet_value_smul,ContinuousMap.smul_apply]
    rw [smul_comm (point.val second) scalar value,
      smul_comm (point.val first) scalar (point.val second • value)]

/-- A genuine vector quadratic monomial in the original Cartesian disk. -/
def quadraticVectorMonomial (dimension : ℕ) (index : Fin 3) :
    ComplexEuclidean dimension →ₗ[ℂ] ClosedJet dimension :=
  ![coordinatePairConstantLinear dimension 0 0,coordinatePairConstantLinear dimension 0 1,
    coordinatePairConstantLinear dimension 1 1] index

def quadraticVectorJet {dimension : ℕ} (data : Fin 3 → ComplexEuclidean dimension) : ClosedJet dimension :=
  ∑ index, quadraticVectorMonomial dimension index (data index)

theorem quadraticVectorJet_value {dimension : ℕ} (data : Fin 3 → ComplexEuclidean dimension) (point : ClosedDisk) :
    (quadraticVectorJet data).value point = (point.val 0 ^ 2) • data 0 +
      (point.val 0 * point.val 1) • data 1 + (point.val 1 ^ 2) • data 2 := by
  simp [quadraticVectorJet,quadraticVectorMonomial,coordinatePairConstantLinear,Fin.sum_univ_three,closedJet_value_add,
    coordinateJet_value,constantValueJet_value,smul_smul,pow_two]

def quadraticVectorAxisCore {parameters : PhaseParameters} {dimension : ℕ}
    (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters dimension) : ACore parameters dimension :=
  ∑ index, vectorAxisProfileCore (quadraticVectorMonomial dimension index) (data index)

def localizedQuadraticVectorAxisCore {parameters : PhaseParameters} {dimension : ℕ}
    (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters dimension) : ACore parameters dimension :=
  ∑ index, vectorAxisProfileCore ((localizedFiniteJetLinear dimension).comp
    (quadraticVectorMonomial dimension index)) (data index)

theorem quadraticVectorAxisCore_val {parameters : PhaseParameters} {dimension : ℕ}
    (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters dimension) (cell : ℤ) :
    (quadraticVectorAxisCore data).val cell = quadraticVectorJet (fun index => (data index).val cell) := by
  simp only [quadraticVectorAxisCore,Submodule.coe_sum,Finset.sum_apply,vectorAxisProfileCore_val,quadraticVectorJet]

theorem localizedQuadraticVectorAxisCore_val {parameters : PhaseParameters} {dimension : ℕ}
    (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters dimension) (cell : ℤ) :
    (localizedQuadraticVectorAxisCore data).val cell =
      localizedFiniteJet (quadraticVectorJet (fun index => (data index).val cell)) := by
  simp only [localizedQuadraticVectorAxisCore,Submodule.coe_sum,Finset.sum_apply,vectorAxisProfileCore_val,
    LinearMap.comp_apply,quadraticVectorJet]
  exact (map_sum (localizedFiniteJetLinear dimension) _ _).symm

/-- The literal cubic scalar coefficient insertion. -/
def cubicScalarAxisCore {parameters : PhaseParameters}
    (data : Fin 4 → Grad.AxisCore.AxisSmoothCore parameters 1) : ACore parameters 1 :=
  ∑ index, fixedAxisJetCore (cubicScalarJet (Pi.single index 1)) (data index)

def localizedCubicScalarAxisCore {parameters : PhaseParameters}
    (data : Fin 4 → Grad.AxisCore.AxisSmoothCore parameters 1) : ACore parameters 1 :=
  ∑ index, fixedAxisJetCore (localizedFiniteJet (cubicScalarJet (Pi.single index 1))) (data index)

theorem cubicScalarAxisCore_val {parameters : PhaseParameters}
    (data : Fin 4 → Grad.AxisCore.AxisSmoothCore parameters 1) (cell : ℤ) :
    (cubicScalarAxisCore data).val cell = cubicScalarJet (fun index => (data index).val cell 0) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro component
  have componentZero : component = 0 := Subsingleton.elim _ _
  subst component
  simp [cubicScalarAxisCore,Fin.sum_univ_four,fixedAxisJetCore_val,
    closedJet_value_add,closedJet_value_smul,cubicScalarJet_value]
  ring

theorem localizedCubicScalarAxisCore_val {parameters : PhaseParameters}
    (data : Fin 4 → Grad.AxisCore.AxisSmoothCore parameters 1) (cell : ℤ) :
    (localizedCubicScalarAxisCore data).val cell =
      localizedFiniteJet (cubicScalarJet (fun index => (data index).val cell 0)) := by
  rw [← cubicScalarAxisCore_val data cell]
  simp only [localizedCubicScalarAxisCore,cubicScalarAxisCore,Submodule.coe_sum,Finset.sum_apply,fixedAxisJetCore_val]
  change (∑ index, (data index).val cell 0 • localizedFiniteJetLinear 1 (cubicScalarJet (Pi.single index 1))) =
    localizedFiniteJetLinear 1 (∑ index, (data index).val cell 0 • cubicScalarJet (Pi.single index 1))
  rw [map_sum]
  simp only [map_smul]

/-- Actual physical quadratic vector before localization. -/
def originalU2Core (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) : ACore parameters 3 :=
  quadraticVectorAxisCore (originalLiftPhysicalUAxis parameters length rho epsilon field low source)

def originalS3Core (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) : ACore parameters 1 :=
  cubicScalarAxisCore (originalLiftS3Axis parameters length rho epsilon field low source)

/-- The same fixed radial cutoff, in the original smooth coefficient core. -/
def originalFiniteLiftU (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) : ACore parameters 3 :=
  localizedQuadraticVectorAxisCore (originalLiftPhysicalUAxis parameters length rho epsilon field low source)

def originalFiniteLiftS (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) : ACore parameters 1 :=
  (∑ index, fixedAxisJetCore (localizedFiniteJet (quadraticScalarJet (Pi.single index 1)))
    (originalScalarHessianAxis source index)) +
    localizedCubicScalarAxisCore (originalLiftS3Axis parameters length rho epsilon field low source)

end Grad.FinitePhysicalJetLift
