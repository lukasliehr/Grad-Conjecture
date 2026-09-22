import AKBI18SameActualCartesianCofactorFlux

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open scoped BigOperators
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.NonlinearProduct Grad.SourceCollar Grad.FinitePhysicalJetLift Grad.AxisSplit
open Grad.OriginalKernelCovariantRecovery Grad.OriginalKernelRetainedDecay
open Grad.GaugeCoefficients.Physical.Ledger

/-- The original L,L,1 Cartesian divergence on the actual smooth core. -/
def originalCartesianDivergenceCore {parameters : PhaseParameters} (length : ℝ) (field : ACore parameters 3) : ACore parameters 1 :=
  (length : ℂ) • (partialCore parameters 0 (valueMapCore parameters (matrixUnit (0 : Fin 1) (0 : Fin 3)) field)+
    partialCore parameters 1 (valueMapCore parameters (matrixUnit (0 : Fin 1) (1 : Fin 3)) field))+
  timeDerivativeCore parameters (valueMapCore parameters (matrixUnit (0 : Fin 1) (2 : Fin 3)) field)

/-- Exact original normalization: the genuine cofactor divergence is the
literal determinant variation, with the SAME affine toroidal derivative. -/
theorem originalCartesianCofactorDivergence (parameters : PhaseParameters) (length : ℝ) (nonzero : length≠0)
    (state : QuotientState parameters) (vector : ACore parameters 3) :
    originalCartesianDivergenceCore length (originalCartesianCofactorFluxCore length state vector)=
      determinantOperation parameters (partialCore parameters 0 vector) (partialCore parameters 1 state.2.1) (affineStateCore parameters length state)+
      determinantOperation parameters (partialCore parameters 0 state.2.1) (partialCore parameters 1 vector) (affineStateCore parameters length state)+
      determinantOperation parameters (partialCore parameters 0 state.2.1) (partialCore parameters 1 state.2.1) (physicalVariationAffine state.1 vector) := by
  rw [originalCartesianDivergenceCore,originalCartesianCofactorFluxCore]
  simp only [originalScalarTripletCore_coordinate,Matrix.cons_val,map_smul,smul_add,
    smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr nonzero)]
  exact originalAffine_piola length state vector

/-- The actual original third quotient row equals the projected genuine
cofactor divergence for every smooth original direction. -/
theorem originalQuotientDeterminant_cofactorDivergence (parameters : PhaseParameters) (length : ℝ) (nonzero : length≠0)
    (state : QuotientState parameters) (vector : ACore parameters 3) (scalar : ACore parameters 1) :
    quotientRowsDerivative parameters length 1 state ![(0,vector,scalar)] 2=
      removeAngularCore parameters (originalCartesianDivergenceCore length (originalCartesianCofactorFluxCore length state vector)) := by
  rw [originalCartesianCofactorDivergence parameters length nonzero,quotientRowsDerivative_etaZero]
  rfl

theorem originalHomogeneous_cartesianCofactorDivergence (parameters : PhaseParameters) (length : ℝ) (nonzero : length≠0)
    (state : QuotientState parameters) (vector : ACore parameters 3) (scalar : ACore parameters 1)
    (homogeneous : quotientRowsDerivative parameters length 1 state ![(0,vector,scalar)]=0) :
    removeAngularCore parameters (originalCartesianDivergenceCore length (originalCartesianCofactorFluxCore length state vector))=0 := by
  rw [← originalQuotientDeterminant_cofactorDivergence parameters length nonzero state vector scalar,homogeneous]
  rfl

end Grad.OriginalKernelHomogeneousGraph
