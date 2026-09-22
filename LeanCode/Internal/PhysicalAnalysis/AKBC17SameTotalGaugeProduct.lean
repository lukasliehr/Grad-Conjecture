import AKBC16OriginalGaugeStorageFidelity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
open scoped BigOperators
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra Grad.SourceCollarFullSource
open Grad.AnnularReconstruction Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.AnnularSmoothCore Grad.AnnularPhysicalReconstruction Grad.BoundaryKernelAction
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.ActualGaugeSigmaPrimitives Grad.ActualPolarFlux Grad.SourceCollar

variable (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact) (r : RadialPoint) (kind : Fin 2)

def originalTotalGaugeProduct (source : ℝ×ℝ→ComplexEuclidean 3) (angles : ℝ×ℝ) : ComplexEuclidean 1 :=
  matrixUnit (0 : Fin 1) (if kind=0 then 1 else 2) (source angles)+
    polarFamilyRowProduct parameters
      (originalGaugeDeviation parameters L state.data.rho state.data.alpha state.data.delta
        state.data.parameter state.data.epsilon state.data.field)
      (if kind=0 then 1 else 2) r.val r.property.1 r.property.2 source angles

theorem originalTotalGaugeProduct_continuous (source : ℝ×ℝ→ComplexEuclidean 3) (continuousSource : Continuous source) :
    Continuous (originalTotalGaugeProduct parameters L compact state r kind source) :=
  ((matrixUnit (0 : Fin 1) (if kind=0 then 1 else 2)).continuous.comp continuousSource).add
    (polarFamilyRowProduct_continuous parameters _
      (originalGaugeDeviation_coherent parameters L state.data.rho state.data.alpha state.data.delta
        state.data.parameter state.data.epsilon state.data.field state.low)
      _ r.val r.property.1 r.property.2 source continuousSource)

theorem originalTotalGaugeProduct_value (source : ℝ×ℝ→ComplexEuclidean 3) (angles : ℝ×ℝ) :
    originalTotalGaugeProduct parameters L compact state r kind source angles 0=
      ∑ component : Fin 3,originalGaugeRow parameters L state.data.rho state.data.alpha state.data.delta
        state.data.parameter state.data.epsilon state.data.field kind angles.2 angles.1
        (polarClosedPoint r.val angles.1 r.property.1 r.property.2) component*source angles component := by
  simp only [originalTotalGaugeProduct,polarFamilyRowProduct,polarFamilyAngleEntry,
    originalGaugeDeviation_matrix parameters L state.data.rho state.data.alpha state.data.delta
      state.data.parameter state.data.epsilon state.data.field state.low,
    polarMatrixEntry_sub,polarMatrixEntry_one,originalGaugeRow]
  simp [matrixUnit_apply,operatorBasis,sub_smul,Finset.sum_sub_distrib]

theorem originalTotalGaugeProduct_periodic (source : ℝ×ℝ→ComplexEuclidean 3)
    (periodic : ∀ polar axial,source (polar+2*Real.pi,axial)=source (polar,axial)) (axial : ℝ) :
    Function.Periodic (fun polar => originalTotalGaugeProduct parameters L compact state r kind source (polar,axial)) (2*Real.pi) := by
  intro polar
  dsimp only [originalTotalGaugeProduct,polarFamilyRowProduct]
  rw [periodic]
  congr 1
  apply Finset.sum_congr rfl
  intro component _
  rw [(polarFamilyAngleEntry_periodic parameters _
    (originalGaugeDeviation_coherent parameters L state.data.rho state.data.alpha state.data.delta
      state.data.parameter state.data.epsilon state.data.field state.low)
    (if kind=0 then 1 else 2) r.val r.property.1 r.property.2 component (polar,axial)).1]

variable (lower : ℝ) (positive : 0<lower) {row : DivisionRow 3 lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower<1) (radius : Icc lower (1 : ℝ))

theorem originalTotalGaugeTrace_coefficient (mode : ℤ×ℤ) :
    negativeTraceCoefficient _ 0 0
      (forceCoordinateTrace (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0 (if kind=0 then 1 else 2)
          (originalCurveNegativeTrace curves radius)+
        fullNegativeKernelAction (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
          (radialGaugeKernel parameters L compact state (tupleRadius lower positive radius) kind 0)
          (originalCurveNegativeTrace curves radius)) mode=
    doubleCoefficient (originalTotalGaugeProduct parameters L compact state (tupleRadius lower positive radius) kind
      (fun angles => curves.fullField bounded (radius.val,angles))) mode := by
  rw [negativeTraceCoefficient_add,originalGaugeNegative_product parameters L compact state lower positive curves bounded radius kind mode]
  rw [forceCoordinateTrace,coordinateProjectionKernel,constantMatrixKernel_action_coefficient,
    originalCurveNegativeTrace_coefficient curves bounded radius]
  have sum := doubleCoefficient_add
    (fun angles => matrixUnit (0 : Fin 1) (if kind=0 then 1 else 2) (curves.fullField bounded (radius.val,angles)))
    (polarFamilyRowProduct parameters
      (originalGaugeDeviation parameters L state.data.rho state.data.alpha state.data.delta
        state.data.parameter state.data.epsilon state.data.field)
      (if kind=0 then 1 else 2) radius.val (positive.le.trans radius.property.1) radius.property.2
      (fun angles => curves.fullField bounded (radius.val,angles)))
    ((matrixUnit (0 : Fin 1) (if kind=0 then 1 else 2)).continuous.comp (curves.fullField_continuous_angles bounded radius.val radius.property))
    (polarFamilyRowProduct_continuous parameters _
      (originalGaugeDeviation_coherent parameters L state.data.rho state.data.alpha state.data.delta
        state.data.parameter state.data.epsilon state.data.field state.low)
      _ radius.val (positive.le.trans radius.property.1) radius.property.2 _
      (curves.fullField_continuous_angles bounded radius.val radius.property)) mode
  rw [doubleCoefficient_valueMap _ _ (curves.fullField_continuous_angles bounded radius.val radius.property)] at sum
  exact sum.symm

end Grad.OriginalKernelCovariantRecovery
