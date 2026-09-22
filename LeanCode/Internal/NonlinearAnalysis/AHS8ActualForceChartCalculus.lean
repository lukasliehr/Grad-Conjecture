import AHS7EncodedCoordinateCalculus

noncomputable section
set_option maxHeartbeats 1800000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger Grad.SourceCollarCoefficients Grad.ActualCurrentPrimitives

theorem angularDerivative_smul_trace {dimension : ℕ} {parameters : PhaseParameters}
    {angular cell : ℕ} {field derivative : NegativeTrace parameters angular cell dimension}
    (law : IsAngularDerivative parameters angular cell field derivative) (scalar : ℂ) :
    IsAngularDerivative parameters angular cell (scalar • field) (scalar • derivative) := by
  intro mode
  rw [negativeTraceCoefficient_smul, negativeTraceCoefficient_smul, law]
  exact smul_comm _ _ _

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
private abbrev rp := radialKernelParameters parameters r

theorem radialForceKernel_derivative (kind : Fin 2) (angular cell : ℕ)
    (input derivative : NegativeTrace (rp parameters r) angular cell 3)
    (differentiated : IsAngularDerivative (rp parameters r) angular cell input derivative) :
    IsAngularDerivative (rp parameters r) angular cell
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialForceKernel parameters L compact state r kind 0) input)
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialRotatedForceKernel parameters L compact state r kind 0) input +
       fullNegativeKernelAction (rp parameters r) angular cell
        (radialForceKernel parameters L compact state r kind 0) derivative) :=
  boundaryRowMultiplicationKernel_derivative (rp parameters r) angular cell 3 _
    (fun component moment => by
      simpa only [radialKernelProductMoment] using
        forceScalarMoment_summable parameters L state.data.rho state.data.epsilon state.data.field
          kind state.low component moment 0 r.val r.property.1 r.property.2)
    (fun component moment => by
      simpa only [radialKernelProductMoment] using
        (rotatedForceScalarMoment_bound parameters L state.data.rho state.data.epsilon
          state.data.field kind state.low component moment 0 r.val r.property.1 r.property.2).1)
    input derivative differentiated

variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialGaugeLowRadius parameters L compact)

theorem radialGaugeQ_first (angular cell : ℕ)
    (input : NegativeTrace (rp parameters r) angular cell 3) :
    forceCoordinateTrace (rp parameters r) angular cell 0
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialGaugeQKernel parameters L compact state r small) input) =
      forceCoordinateTrace (rp parameters r) angular cell 0 input := by
  rw [radialGaugeQKernel_action_eq, map_add]
  have tailZero (tail : NegativeTrace (rp parameters r) angular cell 2) :
      forceCoordinateTrace (rp parameters r) angular cell 0
        (fullNegativeKernelAction (rp parameters r) angular cell (tailInjectionKernel (rp parameters r)) tail) = 0 := by
    apply NegativeTrace.ext_coefficient (rp parameters r) angular cell
    intro mode
    apply PiLp.ext
    intro component
    have unique := Fin.eq_zero component
    subst component
    simp only [forceCoordinateTrace, coordinateProjectionKernel_action_coefficient,
      tailInjectionKernel, constantMatrixKernel_action_coefficient, tailInjectionMap]
    simp [matrixUnit_apply, operatorBasis, negativeTraceCoefficient]
  rw [tailZero, add_zero]

/-- AE10/AE16's same actual chart and its genuine angular derivative. -/
def radialForceChart (angular cell : ℕ)
    (encoded known : NegativeTrace (rp parameters r) angular cell 3) :
    NegativeTrace (rp parameters r) angular cell 3 :=
  fullNegativeKernelAction (rp parameters r) angular cell
    (radialGaugeQKernel parameters L compact state r small)
    (fullNegativeKernelAction (rp parameters r) angular cell (encodedJKernel (rp parameters r)) encoded + known)

def radialForceChartRotation (parameters : PhaseParameters) (r : RadialPoint) (angular cell : ℕ)
    (encoded knownDerivative : NegativeTrace (rp parameters r) angular cell 3) :
    NegativeTrace (rp parameters r) angular cell 3 :=
  fullNegativeKernelAction (rp parameters r) angular cell (encodedRotationKernel (rp parameters r)) encoded + knownDerivative

theorem radialForceChart_derivative (angular cell : ℕ)
    (encoded known knownDerivative : NegativeTrace (rp parameters r) angular cell 3)
    (knownLaw : IsAngularDerivative (rp parameters r) angular cell known knownDerivative) :
    IsAngularDerivative (rp parameters r) angular cell
      (radialForceChart parameters L compact state r small angular cell encoded known)
      (radialForceChartRotation parameters r angular cell encoded knownDerivative) := by
  apply radialGaugeQKernel_derivative
  exact (encodedJKernel_derivative (rp parameters r) angular cell encoded).add knownLaw

/-- Literal AE12 first force row: -Reta-2a1+delta-r0*a. -/
def radialFirstForceTrace (angular cell : ℕ)
    (encoded known : NegativeTrace (rp parameters r) angular cell 3) :
    NegativeTrace (rp parameters r) angular cell 1 :=
  -forceCoordinateTrace (rp parameters r) angular cell 1
    (fullNegativeKernelAction (rp parameters r) angular cell (encodedRotationKernel (rp parameters r)) encoded) -
  (2 : ℂ) • forceCoordinateTrace (rp parameters r) angular cell 0
    (radialForceChart parameters L compact state r small angular cell encoded known) +
  fullNegativeKernelAction (rp parameters r) angular cell
    (radialForceKernel parameters L compact state r 0 0)
    (radialForceChart parameters L compact state r small angular cell encoded known)

def radialFirstForceDerivativeTrace (angular cell : ℕ)
    (encoded known knownDerivative : NegativeTrace (rp parameters r) angular cell 3) :
    NegativeTrace (rp parameters r) angular cell 1 :=
  -forceCoordinateTrace (rp parameters r) angular cell 1 encoded -
  (2 : ℂ) • forceCoordinateTrace (rp parameters r) angular cell 0
    (radialForceChartRotation parameters r angular cell encoded knownDerivative) +
  (fullNegativeKernelAction (rp parameters r) angular cell
    (radialRotatedForceKernel parameters L compact state r 0 0)
    (radialForceChart parameters L compact state r small angular cell encoded known) +
   fullNegativeKernelAction (rp parameters r) angular cell
    (radialForceKernel parameters L compact state r 0 0)
    (radialForceChartRotation parameters r angular cell encoded knownDerivative))

theorem radialFirstForceTrace_derivative (angular cell : ℕ)
    (encoded known knownDerivative : NegativeTrace (rp parameters r) angular cell 3)
    (supported : EncodedSupport (rp parameters r) angular cell encoded)
    (knownLaw : IsAngularDerivative (rp parameters r) angular cell known knownDerivative) :
    IsAngularDerivative (rp parameters r) angular cell
      (radialFirstForceTrace parameters L compact state r small angular cell encoded known)
      (radialFirstForceDerivativeTrace parameters L compact state r small angular cell encoded known knownDerivative) := by
  have chartLaw := radialForceChart_derivative parameters L compact state r small angular cell
    encoded known knownDerivative knownLaw
  exact ((encodedRotation_second_derivative (rp parameters r) angular cell encoded supported).neg.sub
    (angularDerivative_smul_trace (chartLaw.constantMatrix (matrixUnit 0 0)) 2)).add
      (radialForceKernel_derivative parameters L compact state r 0 angular cell _ _ chartLaw)

/-- This exact two-equation encoding is equivalent to the full first force
row, including its angular mean and every cell frequency. -/
theorem radialFirstForceTrace_iff (angular cell : ℕ)
    (encoded known knownDerivative : NegativeTrace (rp parameters r) angular cell 3)
    (source sourceDerivative : NegativeTrace (rp parameters r) angular cell 1)
    (supported : EncodedSupport (rp parameters r) angular cell encoded)
    (knownLaw : IsAngularDerivative (rp parameters r) angular cell known knownDerivative)
    (sourceLaw : IsAngularDerivative (rp parameters r) angular cell source sourceDerivative) :
    radialFirstForceTrace parameters L compact state r small angular cell encoded known = source ↔
      forceMeanTrace (rp parameters r) angular cell
        (radialFirstForceTrace parameters L compact state r small angular cell encoded known) =
        forceMeanTrace (rp parameters r) angular cell source ∧
      radialFirstForceDerivativeTrace parameters L compact state r small angular cell encoded known knownDerivative =
        sourceDerivative :=
  angularDerivative_equal_iff_mean_derivative (rp parameters r) angular cell _ _ _ _
    (radialFirstForceTrace_derivative parameters L compact state r small angular cell
      encoded known knownDerivative supported knownLaw) sourceLaw

end Grad.AnnularReconstruction
