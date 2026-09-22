import AKBC11OriginalPoloidalMean

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set MeasureTheory
open scoped Interval BigOperators
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.SourceCollar Grad.NonlinearRange Grad.NonlinearQuotientBounds Grad.FlatSourceProjection
open Grad.SmoothingFamily Grad.Cor18 Grad.ChartAxisLift Grad.PhysicalCoordinates Grad.GaugeCoefficients.Physical.Frame

variable (parameters : PhaseParameters) (seed : Seed.Parameters) (inside : seed∈Seed.parameterDomain)

/-- Literal original poloidal constraint at every radius and axial angle,
with the physical-to-storage permutation applied exactly once. -/
theorem originalDomain_poloidalMean (vector : ACore parameters 3)
    (constrained : VectorConstraints parameters seed inside (toPhysicalCore parameters vector))
    (radius : ℝ) (bounded : |radius|≤1) (axialAngle : ℝ) :
    sourceAngularAverage (fun polarAngle => polarTangentialComponent polarAngle
      (transposeOperator (harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3) axialAngle)
        (coreValue (planarPartCore parameters (toPhysicalCore parameters vector))
          (polarClosedPoint radius bounded polarAngle) axialAngle)))=0 := by
  have extracted := poloidal_gauge_extraction parameters seed inside _ constrained.2.1
  have averaged := sourceAngularAverage_polarTangential
    (seedTransposeCore parameters seed inside (planarPartCore parameters (toPhysicalCore parameters vector)))
    radius bounded axialAngle
  simp only [sourceCoreValue,coreValue_seedTranspose] at averaged
  rw [averaged,extracted]
  simp [coreValue]

/-- Literal original toroidal constraint, retaining the exact physical
L^-1 seed derivative and full axial Fourier evaluation. -/
theorem originalDomain_toroidalMean (vector : ACore parameters 3)
    (constrained : VectorConstraints parameters seed inside (toPhysicalCore parameters vector))
    (radius : ℝ) (bounded : |radius|≤1) (axialAngle : ℝ) :
    sourceAngularAverage (fun polarAngle =>
      (coreValue (toroidalPartCore parameters (toPhysicalCore parameters vector))
        (polarClosedPoint radius bounded polarAngle) axialAngle +
        (parameters.length⁻¹ : ℂ) •
          ((polarClosedPoint radius bounded polarAngle).val 0 • planarComponentMap 0
            (transposeOperator (deriv (harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3)) axialAngle)
              (coreValue (planarPartCore parameters (toPhysicalCore parameters vector))
                (polarClosedPoint radius bounded polarAngle) axialAngle)) +
           (polarClosedPoint radius bounded polarAngle).val 1 • planarComponentMap 1
            (transposeOperator (deriv (harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3)) axialAngle)
              (coreValue (planarPartCore parameters (toPhysicalCore parameters vector))
                (polarClosedPoint radius bounded polarAngle) axialAngle)))) 0)=0 := by
  let field := toroidalPartCore parameters (toPhysicalCore parameters vector)+
    (parameters.length⁻¹ : ℂ) • derivativeDotCore parameters seed inside
      (planarPartCore parameters (toPhysicalCore parameters vector))
  have extracted : angularCore parameters 0 field=0 := by
    simp only [field,map_add,map_smul]
    exact toroidal_gauge_extraction parameters seed inside _ constrained.2.2.1
  have averaged := sourceAngularAverage_sourceCoreValue_zero field extracted radius bounded axialAngle
  simpa only [field,sourceCoreValue,coreValue_add,coreValue_smul,coreValue_derivativeDot] using averaged

/-- Membership in the project's actual real smooth range supplies the full
original constraint kernel; no additional gauge condition is postulated. -/
theorem originalSmoothDomain_constraints (state : StateCore parameters)
    (member : state∈Grad.RealFixedRanges.stateSmoothRange parameters seed inside) :
    FullConstraints parameters seed inside state := by
  have fixed := ((Grad.RealFixedRanges.mem_stateSmoothRange parameters seed inside state).mp member).1
  have constraints := fullProjection_constraints parameters seed inside state
  rw [fixed] at constraints
  exact constraints

end Grad.OriginalKernelCovariantRecovery
