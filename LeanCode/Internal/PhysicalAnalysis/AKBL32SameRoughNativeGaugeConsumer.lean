import AKBL31SameWeightedGaugeZero

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.BoundaryTrace
open Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation

/-- Same-field Qa recovery from the literal two polar means of the actual
full gauge product. Matrix fidelity, all integer-cell sums, the radial phase,
the rough complement and the retained determinant inverse are discharged.
The remaining specialization is to identify these two literal means with
the already proved original seven-packet native means; no PDE/H1 premise is
inserted to replace that obligation. -/
theorem startupSameRough_current_fromPolarGauges {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (base : ACore parameters 3) (rho epsilon : ℝ)
    (gauge : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3)
    (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge))
    (constants : ℕ → ℝ) (nonnegative : ∀ grade, 0 ≤ constants grade)
    (low : physicalBudget parameters base rho epsilon 6 ≤ 1)
    (bound : ∀ grade, ‖gauge grade‖ ≤ constants grade * physicalBudget parameters base rho epsilon (grade+4))
    (small : physicalBudget parameters base rho epsilon 6 ≤ determinantLowRadius constants)
    (field : StartupL2 3) (raw : ℝ × Spatial → PhysicalValue 3)
    (same : StartupWeightedRep parameters.sigma0 parameters.gamma ell field raw)
    (regular : StartupOrbitContinuous raw)
    (continuousGauge : ∀ cell : ℤ, ContinuousOn
      (fun point => angularCoefficient (fun angle => startupRawMatrix (fullGaugeFamily gauge) raw (angle,point)) cell)
      (openUnitDisk \ {(0 : Spatial)}))
    (gauges : ∀ (radius : ℝ) (_positive : 0 < radius) (_inside : radius < 1) (bounded : |radius| ≤ 1) (cell : ℤ),
      angularCoefficient (fun polar => polarTangentialComponent polar (planarPartMap
        (angularCoefficient (fun angle => startupRawMatrix (fullGaugeFamily gauge) raw
          (angle,(Grad.Constraints.polarClosedPoint radius bounded polar).val)) cell))) 0 = 0 ∧
      angularCoefficient (fun polar => toroidalPartMap
        (angularCoefficient (fun angle => startupRawMatrix (fullGaugeFamily gauge) raw
          (angle,(Grad.Constraints.polarClosedPoint radius bounded polar).val)) cell)) 0 = 0) :
    originalCurrentKernel admissible gauge coherent inverseCoherent (originalCircleKernel field) = field := by
  have gaugeRep := StartupWeightedRep.matrix admissible (fullGaugeFamily gauge)
    (fullGaugeFamily_coherent gauge coherent) same regular
  have zero := startupSameWeighted_gauge_zero parameters.sigma0 parameters.gamma ell
    (originalMatrixKernel admissible (fullGaugeFamily gauge) (fullGaugeFamily_coherent gauge coherent) field)
    (fun cell point => angularCoefficient (fun angle => startupRawMatrix (fullGaugeFamily gauge) raw (angle,point)) cell)
    continuousGauge gaugeRep gauges
  exact startupSameRough_current_recovers parameters admissible base rho epsilon gauge coherent inverseCoherent
    constants nonnegative low bound small field raw same regular zero

end Grad.CartesianStartup
