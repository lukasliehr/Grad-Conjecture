import AHS10ForceEncodingEquivalence

noncomputable section
set_option maxHeartbeats 1800000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

/-- Coordinate equality is equality of the full completed three-field carrier. -/
theorem forceVector_eq_iff (parameters : PhaseParameters) (angular cell : ℕ)
    (first second : NegativeTrace parameters angular cell 3) :
    first = second ↔
      forceCoordinateTrace parameters angular cell 0 first = forceCoordinateTrace parameters angular cell 0 second ∧
      forceCoordinateTrace parameters angular cell 1 first = forceCoordinateTrace parameters angular cell 1 second ∧
      forceCoordinateTrace parameters angular cell 2 first = forceCoordinateTrace parameters angular cell 2 second := by
  constructor
  · intro same
    subst second
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨hzero, hone, htwo⟩
    apply NegativeTrace.ext_coefficient parameters angular cell
    intro mode
    apply PiLp.ext
    intro component
    have each (coordinate : Fin 3)
        (same : forceCoordinateTrace parameters angular cell coordinate first =
          forceCoordinateTrace parameters angular cell coordinate second) :
        negativeTraceCoefficient parameters angular cell first mode coordinate =
          negativeTraceCoefficient parameters angular cell second mode coordinate := by
      have evaluated := congrArg (fun field => negativeTraceCoefficient parameters angular cell field mode 0) same
      simpa only [forceCoordinateTrace, coordinateProjectionKernel_action_coefficient] using evaluated
    fin_cases component
    · exact each 0 hzero
    · exact each 1 hone
    · exact each 2 htwo

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
private abbrev rp := radialKernelParameters parameters r
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialGaugeLowRadius parameters L compact)

def radialForceEncodedDataTrace (angular cell : ℕ)
    (known knownDerivative : NegativeTrace (rp parameters r) angular cell 3)
    (xiZeta sourceZero sourceDerivative sourceTwo : NegativeTrace (rp parameters r) angular cell 1) :
    NegativeTrace (rp parameters r) angular cell 3 :=
  fullNegativeKernelAction (rp parameters r) angular cell (firstCoordinateInjectionKernel (rp parameters r))
    (radialForceDataZero parameters L compact state r small angular cell known sourceZero) +
  (fullNegativeKernelAction (rp parameters r) angular cell (secondCoordinateInjectionKernel (rp parameters r))
    (radialForceDataOne parameters L compact state r small angular cell known knownDerivative sourceDerivative) +
   fullNegativeKernelAction (rp parameters r) angular cell (thirdCoordinateInjectionKernel (rp parameters r))
    (radialForceDataTwo parameters L compact state r small angular cell known xiZeta sourceTwo))

theorem radialForceEncodedDataTrace_coordinates (angular cell : ℕ)
    (known knownDerivative : NegativeTrace (rp parameters r) angular cell 3)
    (xiZeta sourceZero sourceDerivative sourceTwo : NegativeTrace (rp parameters r) angular cell 1) :
    let data := radialForceEncodedDataTrace parameters L compact state r small angular cell
      known knownDerivative xiZeta sourceZero sourceDerivative sourceTwo
    forceCoordinateTrace (rp parameters r) angular cell 0 data =
      radialForceDataZero parameters L compact state r small angular cell known sourceZero ∧
    forceCoordinateTrace (rp parameters r) angular cell 1 data =
      radialForceDataOne parameters L compact state r small angular cell known knownDerivative sourceDerivative ∧
    forceCoordinateTrace (rp parameters r) angular cell 2 data =
      radialForceDataTwo parameters L compact state r small angular cell known xiZeta sourceTwo := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  all_goals
    apply NegativeTrace.ext_coefficient (rp parameters r) angular cell
    intro mode
    apply PiLp.ext
    intro component
    have unique := Fin.eq_zero component
    subst component
    simp only [forceCoordinateTrace, coordinateProjectionKernel_action_coefficient,
      radialForceEncodedDataTrace, negativeTraceCoefficient_add, PiLp.add_apply,
      firstCoordinateInjectionKernel, secondCoordinateInjectionKernel, thirdCoordinateInjectionKernel,
      coordinateInjectionKernel_action_coefficient]
    norm_num [Fin.ext_iff]

/-- AE12 is exactly the already constructed D0+E system, both directions,
with its complete three-coordinate data and unchanged original coefficients. -/
theorem radialForceEncoding_system_iff
    (firstSmall : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
      radialFirstLowRadius parameters L compact) (angular cell : ℕ)
    (encoded known knownDerivative : NegativeTrace (rp parameters r) angular cell 3)
    (xiZeta sourceZero sourceDerivative sourceTwo : NegativeTrace (rp parameters r) angular cell 1)
    (supported : EncodedSupport (rp parameters r) angular cell encoded)
    (knownMean : IsAngularMeanFreeComponent (rp parameters r) angular cell 0 known)
    (knownLaw : IsAngularDerivative (rp parameters r) angular cell known knownDerivative)
    (sourceLaw : IsAngularDerivative (rp parameters r) angular cell sourceZero sourceDerivative) :
    let gaugeSmall := firstSmall.trans (min_le_left _ _)
    (radialFirstForceTrace parameters L compact state r gaugeSmall angular cell encoded known = sourceZero ∧
     radialThirdForceTrace parameters L compact state r gaugeSmall angular cell encoded known xiZeta = sourceTwo) ↔
    fullNegativeKernelAction (rp parameters r) angular cell
      (radialEncodedFirstSystemKernel parameters L compact state r firstSmall) encoded =
    radialForceEncodedDataTrace parameters L compact state r gaugeSmall angular cell
      known knownDerivative xiZeta sourceZero sourceDerivative sourceTwo := by
  dsimp only
  rw [radialForceEncoding_iff parameters L compact state r (firstSmall.trans (min_le_left _ _)) angular cell
    encoded known knownDerivative xiZeta sourceZero sourceDerivative sourceTwo supported knownMean knownLaw sourceLaw,
    forceVector_eq_iff]
  have rows := radialEncodedSystem_scalar_rows parameters L compact state r firstSmall angular cell encoded
  have data := radialForceEncodedDataTrace_coordinates parameters L compact state r
    (firstSmall.trans (min_le_left _ _)) angular cell known knownDerivative xiZeta sourceZero sourceDerivative sourceTwo
  rw [rows.1, rows.2.1, rows.2.2, data.1, data.2.1, data.2.2]

end Grad.AnnularReconstruction
