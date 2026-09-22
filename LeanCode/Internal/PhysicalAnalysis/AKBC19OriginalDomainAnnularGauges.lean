import AKBC18GaugeMeanFourierVanishing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceBoundaryTrace
open Grad.AnnularOriginalSmoothCore Grad.AnnularReconstruction Grad.ActualSmoothPhysicalField Grad.OriginalKernelRetainedDecay
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.SourceCollarFullSource Grad.Cor18 Grad.PhysicalCoordinates Grad.ActualGaugeSigmaPrimitives Grad.SourceCollar

variable (parameters : PhaseParameters) (compact : ℝ)
    (state : RadialCoefficientState parameters parameters.length compact)

/-- The literal four seed coordinates already stored in this coefficient state. -/
def originalCoefficientSeed : Seed.Parameters :=
  ![state.data.rho,state.data.alpha,state.data.delta,state.data.parameter]

/-- The original constrained smooth U supplies the exact two annular gauge
means for its own a=Q^T F^T U. The physical length and seed are unchanged. -/
theorem originalDomain_annularGauges
    (insideSeed : originalCoefficientSeed parameters compact state∈Seed.parameterDomain)
    (vector : ACore parameters 3)
    (constrained : VectorConstraints parameters (originalCoefficientSeed parameters compact state) insideSeed
      (toPhysicalCore parameters vector))
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (radius : Icc lower (1 : ℝ)) :
    radialPhysicalGaugeMeans parameters parameters.length compact state (tupleRadius lower positive radius) 0 0
      (originalCurveNegativeTrace
        (originalPolarCovariantCurves parameters parameters.length state.data.rho state.data.epsilon state.data.field state.low
          lower positive bounded vector) radius)=0 := by
  apply originalGaugeMeans_zero_of_physicalMeans parameters parameters.length compact state lower positive _ bounded radius
  intro kind axial
  simp_rw [originalTotalGaugeProduct_value]
  have values (polar : ℝ) := originalGaugeRow_sameU parameters parameters.length state.data.rho
    state.data.alpha state.data.delta state.data.parameter state.data.epsilon state.data.field state.low
    lower positive bounded vector kind radius.val radius.property (polar,axial)
  refine (congrArg sourceAngularAverage (funext values)).trans ?_
  have nonnegative : 0≤radius.val := positive.le.trans radius.property.1
  have absBound : |radius.val|≤1 := by rw [abs_of_nonneg nonnegative]; exact radius.property.2
  have means := originalDomain_covectorMeans parameters (originalCoefficientSeed parameters compact state) insideSeed
    vector constrained radius.val absBound axial kind
  dsimp only [originalCoefficientSeed,Matrix.cons_val,Matrix.vecHead,Matrix.vecTail] at means
  simpa only [originalCoreCircle,divisionPolarPoint_eq_original] using means


end Grad.OriginalKernelCovariantRecovery
