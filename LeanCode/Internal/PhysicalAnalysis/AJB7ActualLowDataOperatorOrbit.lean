import AJB6GenuineLowTraceDataTranslations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularLowOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularKernelOrbit
open Grad.AnnularKernelL2 Grad.AnnularKernelContinuity Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularCoupledOrbit Grad.AnnularCurrentEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion

section Assembly
variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedAddCommGroup H] [NormedSpace ℂ H]

def fixedOperatorAssembly (output : F →L[ℂ] H) (input : G →L[ℂ] E) : (E →L[ℂ] F) →L[ℂ] (G →L[ℂ] H) :=
  (ContinuousLinearMap.compL ℂ G F H output).comp ((ContinuousLinearMap.compL ℂ G E F).flip input)

theorem complexLinear_hasFDerivAt_comp {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F]
    (mapping : E →L[ℂ] F) (function : P → E) (derivative : P →L[ℝ] E) (point : P)
    (differentiable : HasFDerivAt function derivative point) :
    HasFDerivAt (fun parameter => mapping (function parameter))
      ((mapping.restrictScalars ℝ).comp derivative) point :=
  (mapping.restrictScalars ℝ).hasFDerivAt.comp point differentiable

end Assembly

variable (parameters : PhaseParameters) (length compact lower : ℝ)
  (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
  (state : RetainedInverseState parameters length compact)

/-- SAME original Cauchy residual: stored derivative minus the actual normalized
coefficient generator, together with the genuine unchanged incoming trace. -/
def actualLowDataOperatorOrbit (tau : OrbitParameter) :
    lowEnergyGraph lower length positive →L[ℂ] LowEnergyData lower :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ (LowEnergyBulk lower) LowEnergyBoundary).symm.toContinuousLinearMap.comp
    ((lowStoredCoordinate lower length positive 1 -
      (actualLowGeneratorOrbit parameters length compact lower lengthPositive positive bounded.le state tau).comp
        (lowStoredCoordinate lower length positive 0)).prod
      (lowIncomingTrace lower length positive bounded))

theorem actualLowDataOperatorOrbit_zero :
    actualLowDataOperatorOrbit parameters length compact lower lengthPositive positive bounded state 0 =
      lowCurrentDataOperator parameters length compact lower lengthPositive positive bounded state := by
  unfold actualLowDataOperatorOrbit lowCurrentDataOperator lowCurrentResidual
  rw [actualLowGeneratorOrbit_zero]

/-- Covariance of the literal low differential equation and ADY trace. -/
theorem actualLowDataOperatorOrbit_translation (tau : OrbitParameter)
    (field : lowEnergyGraph lower length positive) :
    actualLowDataOperatorOrbit parameters length compact lower lengthPositive positive bounded state tau
      (lowTranslation lower length positive tau field) =
        lowDataTranslationEquivalence lower tau
          (lowCurrentDataOperator parameters length compact lower lengthPositive positive bounded state field) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ (LowEnergyBulk lower) LowEnergyBoundary).injective
  apply Prod.ext
  · change lowBulkTranslation lower tau (field.val 1) -
      actualLowGeneratorOrbit parameters length compact lower lengthPositive positive bounded.le state tau
        (lowBulkTranslation lower tau (field.val 0)) =
      lowBulkTranslation lower tau
        (field.val 1 - lowCurrentBulk parameters length compact lower lengthPositive positive bounded.le state (field.val 0))
    rw [map_sub, actualLowGeneratorOrbit_translation]
  · exact lowIncomingTrace_translation lower length positive bounded tau field

/-- The SAME AEI22 data operator, conjugated on its actual complete graph
and original Hilbert datum, on the unchanged analytic width. -/
theorem actualLowDataOperatorOrbit_conjugation (tau : OrbitParameter) :
    actualLowDataOperatorOrbit parameters length compact lower lengthPositive positive bounded state tau =
      (lowDataTranslationEquivalence lower tau).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((lowCurrentDataOperator parameters length compact lower lengthPositive positive bounded state).comp
          (lowTranslationEquivalence lower length positive tau).symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro field
  have covariance := actualLowDataOperatorOrbit_translation parameters length compact lower lengthPositive positive bounded state tau
    (lowTranslation lower length positive (-tau) field)
  rw [lowTranslation_inverse] at covariance
  exact covariance

/-- Fixed bulk injection/graph restriction for the actual generator derivative. -/
def lowDataGeneratorAssembly (lower length : ℝ) (positive : 0 < lower) :
    (LowEnergyBulk lower →L[ℂ] LowEnergyBulk lower) →L[ℂ]
      (lowEnergyGraph lower length positive →L[ℂ] LowEnergyData lower) :=
  fixedOperatorAssembly (lowBulkDataInjection lower) (lowStoredCoordinate lower length positive 0)


def lowDataDiagonal (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    lowEnergyGraph lower length positive →L[ℂ] LowEnergyData lower :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ (LowEnergyBulk lower) LowEnergyBoundary).symm.toContinuousLinearMap.comp
    ((lowStoredCoordinate lower length positive 1).prod (lowIncomingTrace lower length positive bounded))

theorem actualLowDataOperatorOrbit_assembly (tau : OrbitParameter) :
    actualLowDataOperatorOrbit parameters length compact lower lengthPositive positive bounded state tau =
      lowDataDiagonal lower length positive bounded -
        lowDataGeneratorAssembly lower length positive
          (actualLowGeneratorOrbit parameters length compact lower lengthPositive positive bounded.le state tau) := by
  apply ContinuousLinearMap.ext
  intro field
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ (LowEnergyBulk lower) LowEnergyBoundary).injective
  apply Prod.ext
  · rfl
  · change lowIncomingTrace lower length positive bounded field = lowIncomingTrace lower length positive bounded field - 0
    rw [sub_zero]

def actualLowDataOperatorDifferential (tau : OrbitParameter) :
    OrbitParameter →L[ℝ] (lowEnergyGraph lower length positive →L[ℂ] LowEnergyData lower) :=
  -((lowDataGeneratorAssembly lower length positive).restrictScalars ℝ).comp
    (actualLowGeneratorDifferential parameters length compact lower lengthPositive positive bounded.le state tau)

/-- Genuine operator-norm derivative of the actual data operator, including
its fixed incoming condition, obtained from the physical coefficient derivative. -/
theorem actualLowDataOperatorOrbit_hasFDerivAt (tau : OrbitParameter) :
    HasFDerivAt (actualLowDataOperatorOrbit parameters length compact lower lengthPositive positive bounded state)
      (actualLowDataOperatorDifferential parameters length compact lower lengthPositive positive bounded state tau) tau := by
  have assembled : HasFDerivAt (fun sigma => lowDataGeneratorAssembly lower length positive
        (actualLowGeneratorOrbit parameters length compact lower lengthPositive positive bounded.le state sigma))
      (((lowDataGeneratorAssembly lower length positive).restrictScalars ℝ).comp
        (actualLowGeneratorDifferential parameters length compact lower lengthPositive positive bounded.le state tau)) tau :=
    complexLinear_hasFDerivAt_comp (P := OrbitParameter)
      (E := LowEnergyBulk lower →L[ℂ] LowEnergyBulk lower)
      (F := lowEnergyGraph lower length positive →L[ℂ] LowEnergyData lower)
      (lowDataGeneratorAssembly lower length positive)
      (actualLowGeneratorOrbit parameters length compact lower lengthPositive positive bounded.le state)
      (actualLowGeneratorDifferential parameters length compact lower lengthPositive positive bounded.le state tau) tau
      (actualLowGeneratorOrbit_hasFDerivAt parameters length compact lower lengthPositive positive bounded.le state tau)
  have formula : actualLowDataOperatorOrbit parameters length compact lower lengthPositive positive bounded state =
      fun sigma => lowDataDiagonal lower length positive bounded -
        lowDataGeneratorAssembly lower length positive
          (actualLowGeneratorOrbit parameters length compact lower lengthPositive positive bounded.le state sigma) := by
    funext sigma
    exact actualLowDataOperatorOrbit_assembly parameters length compact lower lengthPositive positive bounded state sigma
  rw [formula]
  exact HasFDerivAt.const_sub (𝕜 := ℝ) (E := OrbitParameter)
    (F := lowEnergyGraph lower length positive →L[ℂ] LowEnergyData lower) assembled _

end Grad.AnnularLowOrbit
