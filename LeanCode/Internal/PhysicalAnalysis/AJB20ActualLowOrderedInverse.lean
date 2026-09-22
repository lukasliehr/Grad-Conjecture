import AJB12OriginalLowInverseFirstJetBound
import AJA19OrderedInverseBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularLowOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowCompletion Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularKernelOrbit
open Grad.AnnularReconstruction Grad.AnnularInverseCalculus Grad.AnnularHighInverseOrbit
open Grad.GaugeCoefficients.Physical.Allocation

section Generic
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

theorem negativeAssembly_columns (mapping : E →L[ℂ] F) (angular cell : E) :
    -((mapping.restrictScalars ℝ).comp (orbitDifferential angular cell)) =
      orbitColumns (-mapping angular) (-mapping cell) := by
  apply ContinuousLinearMap.ext
  intro step
  change -((mapping.restrictScalars ℝ) (step.1 • angular + step.2 • cell)) = step.1 • (-mapping angular) + step.2 • (-mapping cell)
  rw [map_add, map_smul, map_smul, smul_neg, smul_neg, neg_add]
  rfl

theorem negativeAssembly_columns_of_eq (mapping : E →L[ℂ] F) (differential : OrbitParameter →L[ℝ] E)
    (angular cell : E) (same : differential = orbitDifferential angular cell) :
    -((mapping.restrictScalars ℝ).comp differential) = orbitColumns (-mapping angular) (-mapping cell) := by
  rw [same]
  exact negativeAssembly_columns mapping angular cell
omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] in
theorem negativeAssembly_apply (mapping : E →L[ℂ] F) (angular cell : E) (first second : ℂ) :
    -(mapping (first • angular + second • cell)) = first • (-mapping angular) + second • (-mapping cell) := by
  rw [map_add, map_smul, map_smul, smul_neg, smul_neg, neg_add]

theorem inverseAssembly_columns (inverse : OrbitParameter → F →L[ℂ] E) (point : OrbitParameter)
    (differential : OrbitParameter →L[ℝ] (E →L[ℂ] F)) (angular cell : E →L[ℂ] F)
    (same : differential = orbitColumns angular cell)
    (derivative : HasFDerivAt inverse ((inverseSandwich (inverse point)).comp differential) point) :
    HasFDerivAt inverse (orbitColumns (-((inverse point).comp (angular.comp (inverse point))))
      (-((inverse point).comp (cell.comp (inverse point))))) point := by
  apply derivative.congr_fderiv
  rw [same]
  exact orbitColumns_comp (inverseSandwich (inverse point)) angular cell
end Generic

variable (parameters : PhaseParameters) (length compact lower : ℝ)
  (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
  (state : RetainedInverseState parameters length compact)

/-- The physical coefficient part of the actual Cauchy data operator and all
its translated jets, assembled with the original seven inputs and outputs. -/
def actualLowDataCoefficientJet (angular cell : ℕ) (tau : OrbitParameter) :
    lowEnergyGraph lower length positive →L[ℂ] LowEnergyData lower :=
  -lowDataGeneratorAssembly lower length positive
    (actualLowResponseOrbitJet parameters length compact lower lengthPositive positive bounded.le state tau angular cell)

theorem actualLowDataCoefficientJet_hasFDerivAt (angular cell : ℕ) (tau : OrbitParameter) :
    HasFDerivAt (actualLowDataCoefficientJet parameters length compact lower lengthPositive positive bounded state angular cell)
      (orbitColumns
        (actualLowDataCoefficientJet parameters length compact lower lengthPositive positive bounded state (angular + 1) cell tau)
        (actualLowDataCoefficientJet parameters length compact lower lengthPositive positive bounded state angular (cell + 1) tau)) tau := by
  have derivative := complexLinear_hasFDerivAt_comp (P := OrbitParameter)
    (E := LowEnergyBulk lower →L[ℂ] LowEnergyBulk lower)
    (F := lowEnergyGraph lower length positive →L[ℂ] LowEnergyData lower)
    (-lowDataGeneratorAssembly lower length positive)
    (fun sigma => actualLowResponseOrbitJet parameters length compact lower lengthPositive positive bounded.le state sigma angular cell)
    _ tau (actualLowResponseOrbitJet_hasFDerivAt parameters length compact lower lengthPositive positive bounded.le state tau angular cell)
  apply derivative.congr_fderiv
  exact orbitDifferential_comp
    (E := LowEnergyBulk lower →L[ℂ] LowEnergyBulk lower)
    (F := lowEnergyGraph lower length positive →L[ℂ] LowEnergyData lower)
    ((-lowDataGeneratorAssembly lower length positive).restrictScalars ℝ) _ _

theorem actualLowDataOperatorDifferential_columns (tau : OrbitParameter) :
    actualLowDataOperatorDifferential parameters length compact lower lengthPositive positive bounded state tau =
      orbitColumns (E := lowEnergyGraph lower length positive →L[ℂ] LowEnergyData lower)
        (actualLowDataCoefficientJet parameters length compact lower lengthPositive positive bounded state 1 0 tau)
        (actualLowDataCoefficientJet parameters length compact lower lengthPositive positive bounded state 0 1 tau) := by
  apply ContinuousLinearMap.ext
  intro direction
  apply ContinuousLinearMap.ext
  intro field
  change -(lowBulkDataInjection lower
    (actualLowGeneratorDifferential parameters length compact lower lengthPositive positive bounded.le state tau direction (field.val 0))) =
      (direction.1 : ℂ) • (-lowBulkDataInjection lower
        (actualLowResponseOrbitJet parameters length compact lower lengthPositive positive bounded.le state tau 1 0 (field.val 0))) +
      (direction.2 : ℂ) • (-lowBulkDataInjection lower
        (actualLowResponseOrbitJet parameters length compact lower lengthPositive positive bounded.le state tau 0 1 (field.val 0)))
  have columns := congrArg (fun differential : OrbitParameter →L[ℝ] (LowEnergyBulk lower →L[ℂ] LowEnergyBulk lower) => differential direction (field.val 0))
    (actualLowGeneratorDifferential_columns parameters length compact lower lengthPositive positive bounded.le state tau)
  have mapped := congrArg (fun value : LowEnergyBulk lower => -lowBulkDataInjection lower value) columns
  exact mapped.trans (negativeAssembly_apply (E := LowEnergyBulk lower) (F := LowEnergyData lower)
    (lowBulkDataInjection lower)
    (actualLowResponseOrbitJet parameters length compact lower lengthPositive positive bounded.le state tau 1 0 (field.val 0))
    (actualLowResponseOrbitJet parameters length compact lower lengthPositive positive bounded.le state tau 0 1 (field.val 0))
    (direction.1 : ℂ) (direction.2 : ℂ))

variable (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
  lowCurrentNeighborhood parameters length compact)
include small

theorem actualLowInverseOrbit_columns (tau : OrbitParameter) :
    let inverse := actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state
    let jet := actualLowDataCoefficientJet parameters length compact lower lengthPositive positive bounded state
    HasFDerivAt inverse (orbitColumns (E := LowEnergyData lower →L[ℂ] lowEnergyGraph lower length positive) (-((inverse tau).comp ((jet 1 0 tau).comp (inverse tau))))
      (-((inverse tau).comp ((jet 0 1 tau).comp (inverse tau))))) tau := by
  exact inverseAssembly_columns (E := lowEnergyGraph lower length positive) (F := LowEnergyData lower)
    (actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state) tau
    (actualLowDataOperatorDifferential parameters length compact lower lengthPositive positive bounded state tau)
    (actualLowDataCoefficientJet parameters length compact lower lengthPositive positive bounded state 1 0 tau)
    (actualLowDataCoefficientJet parameters length compact lower lengthPositive positive bounded state 0 1 tau)
    (actualLowDataOperatorDifferential_columns parameters length compact lower lengthPositive positive bounded state tau)
    (actualLowInverseOrbit_hasFDerivAt parameters length compact lower lengthPositive positive bounded state small tau)

/-- Every ordered angular/cell derivative is the actual fderiv recursion of
SAME AEI24, and the finite formula retains the order of every operator factor. -/
theorem actualLowInverseOrbit_orderedFormula (word : List Bool) (tau : OrbitParameter) :
    orderedOrbitDerivative word (actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state) tau =
      (inverseDerivativeWord word).eval
        (actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state)
        (actualLowDataCoefficientJet parameters length compact lower lengthPositive positive bounded state) tau :=
  orderedOrbitDerivative_inverse (E := lowEnergyGraph lower length positive) (F := LowEnergyData lower)
    (actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state)
    (actualLowDataCoefficientJet parameters length compact lower lengthPositive positive bounded state)
    (actualLowInverseOrbit_columns parameters length compact lower lengthPositive positive bounded state small)
    (actualLowDataCoefficientJet_hasFDerivAt parameters length compact lower lengthPositive positive bounded state) word tau

end Grad.AnnularLowOrbit
