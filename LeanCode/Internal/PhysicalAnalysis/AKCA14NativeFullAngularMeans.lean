import AKCA13OriginalGaugeMeanConverses
import AKBQ9ActualObservedNativeGauges

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set
open scoped BigOperators
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource Grad.SourceCollar
open Grad.ActualSmoothPhysicalField Grad.OriginalKernelCovariantRecovery
open Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.AnnularReconstruction Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.ActualGaugeSigmaPrimitives Grad.ActualPhysicalField Grad.ActualPolarFlux Grad.AnnularPhysicalReconstruction Grad.AnnularSmoothCore Grad.AnnularOriginalSmoothCore

 theorem fullAngularMean_zero_of_cellMeans {dimension : ℕ} (field : ℝ×ℝ→ComplexEuclidean dimension)
    (continuousField : Continuous field)
    (periodicCell : ∀ polar,Function.Periodic (fun axial => field (polar,axial)) (2*Real.pi))
    (meanCells : ∀ cell,angularCoefficient (fun polar => angularCoefficient (fun axial => field (polar,axial)) cell) 0=0)
    (axial : ℝ) : angularCoefficient (fun polar => field (polar,axial)) 0=0 := by
  have equality : (fun axial => angularCoefficient (fun polar => field (polar,axial)) 0)=fun _ => 0 := by
    apply periodicFourier_ext _ _
      (Grad.SourceCollarFullSource.angularCoefficient_continuous_parameter (fun pair => field (pair.2,pair.1)) (continuousField.comp continuous_swap) 0)
      continuous_const
    · intro current
      exact congrArg (fun source : ℝ→ComplexEuclidean dimension => angularCoefficient source 0)
        (funext (fun polar => periodicCell polar current))
    · exact fun _ => rfl
    · intro cell
      rw [← doubleCoefficient_swap field continuousField,meanCells,angularCoefficient_zero]
  exact congrFun equality axial

 theorem physicalAngularMean_zero_of_cellMeans (field : ℝ×ℝ→ComplexEuclidean 1)
    (continuousField : Continuous field)
    (periodicPolar : ∀ axial,Function.Periodic (fun polar => field (polar,axial)) (2*Real.pi))
    (periodicCell : ∀ polar,Function.Periodic (fun axial => field (polar,axial)) (2*Real.pi))
    (meanCells : ∀ cell,angularCoefficient (fun polar => angularCoefficient (fun axial => field (polar,axial)) cell) 0=0)
    (axial : ℝ) : sourceAngularAverage (fun polar => field (polar,axial) 0)=0 := by
  rw [sourceAngularAverage_eq_coefficient _ (fun polar => congrArg (fun value : ComplexEuclidean 1 => value 0) (periodicPolar axial polar)),
    ← angularCoefficient_component (fun polar => field (polar,axial)) (continuousField.comp (continuous_id.prodMk continuous_const)) 0 0,
    fullAngularMean_zero_of_cellMeans field continuousField periodicCell meanCells axial]
  rfl

 theorem originalTotalGaugeProduct_cell_periodic (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact) (radius : RadialPoint) (kind : Fin 2)
    (source : ℝ×ℝ→ComplexEuclidean 3)
    (periodic : ∀ polar axial,source (polar,axial+2*Real.pi)=source (polar,axial)) (polar : ℝ) :
    Function.Periodic (fun axial => originalTotalGaugeProduct parameters L compact state radius kind source (polar,axial)) (2*Real.pi) := by
  intro axial
  dsimp only [originalTotalGaugeProduct,polarFamilyRowProduct]
  rw [periodic]
  congr 1
  apply Finset.sum_congr rfl
  intro component _
  rw [(polarFamilyAngleEntry_periodic parameters _
    (originalGaugeDeviation_coherent parameters L state.data.rho state.data.alpha state.data.delta
      state.data.parameter state.data.epsilon state.data.field state.low)
    (if kind=0 then 1 else 2) radius.val radius.property.1 radius.property.2 component (polar,axial)).2]

 theorem originalGaugeProduct_sameCorrectedU (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact) (lower : ℝ) (positive : 0 < lower) (bounded : lower<1)
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (radius : Icc lower (1 : ℝ)) (kind : Fin 2) (angles : ℝ×ℝ) :
    originalTotalGaugeProduct parameters L compact state (tupleRadius lower positive radius) kind
      (fun angles => curves.fullField bounded (radius.val,angles)) angles 0=
    ∑ coordinate : Fin 3,
      physicalGaugeCovector (physicalSeedMatrix state.data.rho state.data.alpha state.data.delta state.data.parameter angles.2)
        ((L : ℂ)⁻¹ • operatorMatrix (deriv (Grad.GaugeCoefficients.Physical.Frame.harmonicSeedOperator
          state.data.rho state.data.alpha state.data.delta state.data.parameter) angles.2))
        angles.1 (polarClosedPoint radius.val angles.1 (positive.le.trans radius.property.1) radius.property.2) kind coordinate *
        (curves.physicalUFromPolar parameters L state.data.rho state.data.epsilon state.data.field state.low lower positive bounded).fullField
          bounded (radius.val,angles) coordinate := by
  rw [originalTotalGaugeProduct_value]
  simp_rw [originalGaugeRow_covector]
  rw [originalPolarMatrixPairing,curves.fullField_physicalUFromPolar parameters L state.data.rho state.data.epsilon state.data.field
    state.low lower positive bounded radius.val radius.property angles,
    originalInverseTransposeFamily_matrix parameters L state.data.rho state.data.epsilon state.data.field state.low,
    originalInverseFamily_eq_matrixInverse parameters L state.data.rho state.data.epsilon state.data.field state.low]
  rfl

end Grad.OriginalCoreRealization
