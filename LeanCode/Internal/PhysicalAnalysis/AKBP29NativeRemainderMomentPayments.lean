import AKBP28NativeMomentAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.Constraints Grad.Constraints.Gauges Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- The fixed tensor preserves each moment of its actual input rows. These
rows are native completed coefficient outputs, not a diagonalized matrix. -/
theorem startupNativeTensor_moment (force flux : StartupMoments 2) (scalar : StartupMoments 1)
    (grade : Fin 3) (outer inside : Fin 2) :
    StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell ^ grade.val)
      (startupThreeRowTensor (force.moment grade) (scalar.moment grade) (flux.moment grade) outer inside)
      (startupThreeRowTensor force.field scalar.field flux.field outer inside) :=
  (force.related grade).threeRowTensor (fun _ _ _ _ => rfl) (scalar.related grade) (flux.related grade) outer inside

theorem startupNativeTensor_phase {symbol : ℤ → Spatial → ℝ}
    (radial : ∀ cell (first second : Spatial), ‖first‖ = ‖second‖ → symbol cell first = symbol cell second)
    (force flux rawForce rawFlux : StartupMoments 2) (scalar rawScalar : StartupMoments 1)
    (forceSame : StartupRadialRelated symbol force.field rawForce.field)
    (scalarSame : StartupRadialRelated symbol scalar.field rawScalar.field)
    (fluxSame : StartupRadialRelated symbol flux.field rawFlux.field)
    (outer inside : Fin 2) :
    StartupRadialRelated symbol (startupThreeRowTensor force.field scalar.field flux.field outer inside)
      (startupThreeRowTensor rawForce.field rawScalar.field rawFlux.field outer inside) :=
  forceSame.threeRowTensor radial scalarSame fluxSame outer inside

def startupNativeLowerFlux (scale : ℝ) (determinant scalar scalarFlux : StartupMoments 1)
    (gradient : StartupMoments 2) (direction : Fin 2) : StartupL2 3 :=
  startupERLowerFlux (startupERLowerScalar scale determinant.field (scalar.moment 1) (scalarFlux.moment 1))
    (startupAxialField scale (gradient.moment 1)) direction

def startupNativeLowerFluxFirst (scale : ℝ) (determinant scalar scalarFlux : StartupMoments 1)
    (gradient : StartupMoments 2) (direction : Fin 2) : StartupL2 3 :=
  startupERLowerFlux (startupERLowerScalar scale (determinant.moment 1) (scalar.moment 2) (scalarFlux.moment 2))
    (startupAxialField scale (gradient.moment 2)) direction

/-- The one phase derivative of the lower flux uses exactly the native
second moment; no third moment or first spatial derivative is requested. -/
theorem startupNativeLowerFlux_first (scale : ℝ) (determinant scalar scalarFlux : StartupMoments 1)
    (gradient : StartupMoments 2) (direction : Fin 2) :
    StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell)
      (startupNativeLowerFluxFirst scale determinant scalar scalarFlux gradient direction)
      (startupNativeLowerFlux scale determinant scalar scalarFlux gradient direction) :=
  (StartupRadialRelated.lowerScalar scale determinant.first_related scalar.second_first_related scalarFlux.second_first_related).lowerFlux
    (fun _ _ _ _ => rfl) (gradient.second_first_related.axial scale) direction

theorem startupNativeLowerFlux_phase {symbol : ℤ → Spatial → ℝ}
    (radial : ∀ cell (first second : Spatial), ‖first‖ = ‖second‖ → symbol cell first = symbol cell second)
    (scale : ℝ) (determinant scalar scalarFlux rawDeterminant rawScalar rawScalarFlux : StartupMoments 1)
    (gradient rawGradient : StartupMoments 2)
    (detSame : StartupRadialRelated symbol determinant.field rawDeterminant.field)
    (scalarSame : StartupRadialRelated symbol scalar.field rawScalar.field)
    (fluxSame : StartupRadialRelated symbol scalarFlux.field rawScalarFlux.field)
    (gradientSame : StartupRadialRelated symbol gradient.field rawGradient.field) (direction : Fin 2) :
    StartupRadialRelated symbol (startupNativeLowerFlux scale determinant scalar scalarFlux gradient direction)
      (startupNativeLowerFlux scale rawDeterminant rawScalar rawScalarFlux rawGradient direction) :=
  (StartupRadialRelated.lowerScalar scale detSame
    (scalar.phase_moment rawScalar scalarSame 1) (scalarFlux.phase_moment rawScalarFlux fluxSame 1)).lowerFlux radial
      ((gradient.phase_moment rawGradient gradientSame 1).axial scale) direction

end Grad.CartesianStartup
