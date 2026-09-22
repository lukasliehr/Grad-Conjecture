import AKU23FullAxisCovectorAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisJet Grad.FlatSourceProjection Grad.QuotientProjection Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger Grad.NonlinearDivision

def axisComponent {parameters : PhaseParameters} {dimension : ℕ} (component : Fin dimension) :
    Grad.AxisCore.AxisSmoothCore parameters dimension →ₗ[ℂ] Grad.AxisCore.AxisSmoothCore parameters 1 :=
  axisValueMap (componentValue dimension component)

def axisCovectorTriple {parameters : PhaseParameters}
    (planar : Grad.AxisCore.AxisSmoothCore parameters 2) (toroidal : Grad.AxisCore.AxisSmoothCore parameters 1) :
    Grad.AxisCore.AxisSmoothCore parameters 3 :=
  axisValueMap (matrixOperator firstTwoInclusion) planar +
    axisValueMap (matrixOperator (!![0;0;1] : Matrix (Fin 3) (Fin 1) ℂ)) toroidal

def axisQuadraticDivergence {parameters : PhaseParameters} (data : PlanarQuadraticAxisData parameters) :
    Grad.AxisCore.AxisSmoothCore parameters 2 :=
  scalarAxisPair ((2 : ℂ) • axisComponent 0 (data 0) + axisComponent 1 (data 1))
    (axisComponent 0 (data 1) + (2 : ℂ) • axisComponent 1 (data 2))

def axisCubicComplementVector {parameters : PhaseParameters} (linear : Grad.AxisCore.AxisSmoothCore parameters 2) :
    PlanarQuadraticAxisData parameters :=
  ![scalarAxisPair ((5/3 : ℂ) • axisComponent 1 linear) (-(7/3 : ℂ) • axisComponent 0 linear),
    scalarAxisPair ((2/3 : ℂ) • axisComponent 0 linear) (-(2/3 : ℂ) • axisComponent 1 linear),
    scalarAxisPair ((7/3 : ℂ) • axisComponent 1 linear) (-(5/3 : ℂ) • axisComponent 0 linear)]

/-- The full cubic target built from the literal source and the same full
metric coefficients; its first term is L^-1 det(F^-1)g1=-(Ld)^-1g1. -/
def originalCubicTargetAxis (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) : Grad.AxisCore.AxisSmoothCore parameters 2 :=
  let oldLow := (originalCubic_low_margin parameters length rho epsilon field low).1
  let determinantCoherent := (originalAxisInverseDeterminantFamily_estimate parameters length rho epsilon field oldLow).actualCoherent
  let determinantAction := axisFamilyAction (originalAxisInverseDeterminantFamily parameters length epsilon field) determinantCoherent
  let metricCoherent := (originalAxisMetricRowsFamily_estimate parameters length rho epsilon field oldLow).actualCoherent
  let metricAction := axisFamilyAction (originalAxisMetricRowsFamily parameters length epsilon field) metricCoherent
  (length : ℂ)⁻¹ • scalarAxisPair (determinantAction (traceFirst 0 (source 2))) (determinantAction (traceFirst 1 (source 2))) -
    axisQuadraticDivergence (fun index => metricAction (axisCovectorTriple
      (-(quadraticAxisPlanarInverse (originalForce2Axis source) index)) (originalC2Axis length source index)))

def originalLiftEllAxis (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) : Grad.AxisCore.AxisSmoothCore parameters 2 :=
  axisFamilyAction (originalCubicInverseFamily parameters length epsilon field)
    (originalCubicInverseFamily_coherent parameters length rho epsilon field low)
    (originalCubicTargetAxis parameters length rho epsilon field low source)

def originalLiftPlanarAxis (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) : PlanarQuadraticAxisData parameters :=
  axisCubicComplementVector (originalLiftEllAxis parameters length rho epsilon field low source) -
    quadraticAxisPlanarInverse (originalForce2Axis source)

def originalLiftPhysicalUAxis (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters 3 :=
  fun index => axisFamilyAction (originalAxisInverseTransposeFamily parameters length epsilon field)
    (originalAxisInverseTransposeFamily_estimate parameters length rho epsilon field
      (originalCubic_low_margin parameters length rho epsilon field low).1).actualCoherent
    (axisCovectorTriple (originalLiftPlanarAxis parameters length rho epsilon field low source index)
      (originalC2Axis length source index))

def originalLiftS3Axis (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) : Fin 4 → Grad.AxisCore.AxisSmoothCore parameters 1 :=
  let linear := originalLiftEllAxis parameters length rho epsilon field low source
  let planar := originalLiftPlanarAxis parameters length rho epsilon field low source
  ![axisComponent 0 linear + axisComponent 1 (planar 0),
    axisComponent 1 linear + axisComponent 1 (planar 1) - axisComponent 0 (planar 0),
    axisComponent 0 linear + axisComponent 1 (planar 2) - axisComponent 0 (planar 1),
    axisComponent 1 linear - axisComponent 0 (planar 2)]

end Grad.FinitePhysicalJetLift
