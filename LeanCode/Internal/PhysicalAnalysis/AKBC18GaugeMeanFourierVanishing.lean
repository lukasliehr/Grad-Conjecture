import AKBC17SameTotalGaugeProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.OriginalKernelCovariantRecovery
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.SourceCollarFullSource
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.ActualSmoothPhysicalField Grad.SourceCollar Grad.AnnularOriginalSmoothCore

theorem originalDoubleCoefficient_meanZero (source : ℝ×ℝ→ComplexEuclidean 1)
    (continuousSource : Continuous source)
    (periodic : ∀ axial,Function.Periodic (fun polar => source (polar,axial)) (2*Real.pi))
    (mean : ∀ axial,sourceAngularAverage (fun polar => source (polar,axial) 0)=0) (cell : ℤ) :
    doubleCoefficient source (0,cell)=0 := by
  unfold doubleCoefficient
  rw [doubleCoefficient_swap source continuousSource]
  have zero (axial : ℝ) : angularCoefficient (fun polar => source (polar,axial)) 0=0 := by
    apply PiLp.ext
    intro coordinate
    have only := Fin.eq_zero coordinate
    subst coordinate
    exact (angularCoefficient_component (fun polar => source (polar,axial))
      (continuousSource.comp (continuous_id.prodMk continuous_const)) 0 0).trans
        ((sourceAngularAverage_eq_coefficient _ (fun polar =>
          congrArg (fun value : ComplexEuclidean 1 => value 0) (periodic axial polar))).symm.trans (mean axial))
  simp_rw [zero]
  simp [angularCoefficient_constant]

theorem originalMeanTrace_zero_of_coefficients (parameters : PhaseParameters) (angular cell : ℕ)
    (field : NegativeTrace parameters angular cell 1)
    (zero : ∀ axial,negativeTraceCoefficient parameters angular cell field (0,axial)=0) :
    forceMeanTrace parameters angular cell field=0 := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  simp only [forceMeanTrace,angularMeanKernel,scalarModeDiagonalKernel_action_coefficient]
  by_cases same : mode.1=0
  · rw [show mode=(0,mode.2) from Prod.ext same rfl,zero]
    simp [negativeTraceCoefficient]
  · simp [angularMeanMultiplier,same,negativeTraceCoefficient]

variable (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact) (lower : ℝ) (positive : 0<lower)
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower<1) (radius : Icc lower (1 : ℝ))

/-- The original physical circle means imply exactly the two annular gauge
constraints on the same trace, with no weighted-membership premise. -/
theorem originalGaugeMeans_zero_of_physicalMeans
    (mean : ∀ kind axial,sourceAngularAverage (fun polar =>
      originalTotalGaugeProduct parameters L compact state (tupleRadius lower positive radius) kind
        (fun angles => curves.fullField bounded (radius.val,angles)) (polar,axial) 0)=0) :
    radialPhysicalGaugeMeans parameters L compact state (tupleRadius lower positive radius) 0 0
      (originalCurveNegativeTrace curves radius)=0 := by
  have scalarZero (kind : Fin 2) :
      forceMeanTrace (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
        (forceCoordinateTrace (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0 (if kind=0 then 1 else 2)
            (originalCurveNegativeTrace curves radius)+
          fullNegativeKernelAction (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
            (radialGaugeKernel parameters L compact state (tupleRadius lower positive radius) kind 0)
            (originalCurveNegativeTrace curves radius))=0 := by
    apply originalMeanTrace_zero_of_coefficients
    intro axial
    rw [originalTotalGaugeTrace_coefficient parameters L compact state kind lower positive curves bounded radius]
    apply originalDoubleCoefficient_meanZero
    · exact originalTotalGaugeProduct_continuous parameters L compact state (tupleRadius lower positive radius) kind _
        (curves.fullField_continuous_angles bounded radius.val radius.property)
    · exact originalTotalGaugeProduct_periodic parameters L compact state (tupleRadius lower positive radius) kind _
        (curves.fullField_angular_shift bounded radius.val)
    · exact mean kind
  apply NegativeTrace.ext_coefficient _ 0 0
  intro mode
  apply PiLp.ext
  intro kind
  have coordinate := congrArg (fun trace => negativeTraceCoefficient
    (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0 trace mode 0)
    (originalGaugeMeans_coordinate parameters L compact state (tupleRadius lower positive radius) 0 0
      (originalCurveNegativeTrace curves radius) kind)
  rw [coordinateProjectionKernel_action_coefficient,scalarZero] at coordinate
  exact coordinate

end Grad.OriginalKernelCovariantRecovery
