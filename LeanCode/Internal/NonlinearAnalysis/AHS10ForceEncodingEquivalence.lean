import AHS9EncodedForceScalarRows

noncomputable section
set_option maxHeartbeats 1800000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
private abbrev rp := radialKernelParameters parameters r
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialGaugeLowRadius parameters L compact)

/-- AE17's data, for any actual free chart q_* and its genuine derivative. -/
def radialForceDataZero (angular cell : ℕ)
    (known : NegativeTrace (rp parameters r) angular cell 3)
    (source : NegativeTrace (rp parameters r) angular cell 1) : NegativeTrace (rp parameters r) angular cell 1 :=
  forceMeanTrace (rp parameters r) angular cell source -
  forceMeanTrace (rp parameters r) angular cell
    (fullNegativeKernelAction (rp parameters r) angular cell (radialForceKernel parameters L compact state r 0 0)
      (fullNegativeKernelAction (rp parameters r) angular cell (radialGaugeQKernel parameters L compact state r small) known))

def radialForceDataOne (angular cell : ℕ)
    (known knownDerivative : NegativeTrace (rp parameters r) angular cell 3)
    (sourceDerivative : NegativeTrace (rp parameters r) angular cell 1) : NegativeTrace (rp parameters r) angular cell 1 :=
  sourceDerivative + (2 : ℂ) • forceCoordinateTrace (rp parameters r) angular cell 0 knownDerivative -
  forceMeanFreeTrace (rp parameters r) angular cell
    (fullNegativeKernelAction (rp parameters r) angular cell (radialRotatedForceKernel parameters L compact state r 0 0)
      (fullNegativeKernelAction (rp parameters r) angular cell (radialGaugeQKernel parameters L compact state r small) known) +
     fullNegativeKernelAction (rp parameters r) angular cell (radialForceKernel parameters L compact state r 0 0) knownDerivative)

def radialForceDataTwo (angular cell : ℕ)
    (known : NegativeTrace (rp parameters r) angular cell 3)
    (xiZeta source : NegativeTrace (rp parameters r) angular cell 1) : NegativeTrace (rp parameters r) angular cell 1 :=
  source + (L : ℂ)⁻¹ • xiZeta -
  forceMeanFreeTrace (rp parameters r) angular cell
    (fullNegativeKernelAction (rp parameters r) angular cell (radialForceKernel parameters L compact state r 1 0)
      (fullNegativeKernelAction (rp parameters r) angular cell (radialGaugeQKernel parameters L compact state r small) known))

/-- Literal AE12 third row, with its original L^-1 xi_zeta term. -/
def radialThirdForceTrace (angular cell : ℕ)
    (encoded known : NegativeTrace (rp parameters r) angular cell 3)
    (xiZeta : NegativeTrace (rp parameters r) angular cell 1) : NegativeTrace (rp parameters r) angular cell 1 :=
  forceCoordinateTrace (rp parameters r) angular cell 2 encoded +
  forceMeanFreeTrace (rp parameters r) angular cell
    (fullNegativeKernelAction (rp parameters r) angular cell (radialForceKernel parameters L compact state r 1 0)
      (radialForceChart parameters L compact state r small angular cell encoded known)) -
  (L : ℂ)⁻¹ • xiZeta

theorem radialFirstForceTrace_mean_split (angular cell : ℕ)
    (encoded known : NegativeTrace (rp parameters r) angular cell 3)
    (supported : EncodedSupport (rp parameters r) angular cell encoded)
    (knownMean : IsAngularMeanFreeComponent (rp parameters r) angular cell 0 known) :
    forceMeanTrace (rp parameters r) angular cell
      (radialFirstForceTrace parameters L compact state r small angular cell encoded known) =
    radialEncodedRowZero parameters L compact state r small angular cell encoded +
    forceMeanTrace (rp parameters r) angular cell
      (fullNegativeKernelAction (rp parameters r) angular cell (radialForceKernel parameters L compact state r 0 0)
        (fullNegativeKernelAction (rp parameters r) angular cell (radialGaugeQKernel parameters L compact state r small) known)) := by
  rw [radialFirstForceTrace_mean parameters L compact state r small angular cell encoded known supported knownMean,
    radialForceChart_split, map_add, map_add]
  unfold radialEncodedRowZero
  abel

theorem radialFirstForceDerivativeTrace_split (angular cell : ℕ)
    (encoded known knownDerivative : NegativeTrace (rp parameters r) angular cell 3)
    (knownLaw : IsAngularDerivative (rp parameters r) angular cell known knownDerivative) :
    radialFirstForceDerivativeTrace parameters L compact state r small angular cell encoded known knownDerivative =
    radialEncodedRowOne parameters L compact state r small angular cell encoded -
    (2 : ℂ) • forceCoordinateTrace (rp parameters r) angular cell 0 knownDerivative +
    forceMeanFreeTrace (rp parameters r) angular cell
      (fullNegativeKernelAction (rp parameters r) angular cell (radialRotatedForceKernel parameters L compact state r 0 0)
        (fullNegativeKernelAction (rp parameters r) angular cell (radialGaugeQKernel parameters L compact state r small) known) +
       fullNegativeKernelAction (rp parameters r) angular cell (radialForceKernel parameters L compact state r 0 0) knownDerivative) := by
  have decodedLaw := radialGaugeQKernel_derivative parameters L compact state r small angular cell _ _
    (encodedJKernel_derivative (rp parameters r) angular cell encoded)
  have decodedProduct := radialForceKernel_derivative parameters L compact state r 0 angular cell _ _ decodedLaw
  have knownProduct := radialForceKernel_derivative parameters L compact state r 0 angular cell _ _
    (radialGaugeQKernel_derivative parameters L compact state r small angular cell _ _ knownLaw)
  unfold radialEncodedRowOne
  simp only [radialGaugeDecodedKernel, fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
  rw [angularMeanFreeKernel_action_eq _ _ _ _ decodedProduct.meanFree,
    angularMeanFreeKernel_action_eq _ _ _ _ knownProduct.meanFree]
  unfold radialFirstForceDerivativeTrace radialForceChartRotation
  rw [radialForceChart_split]
  simp only [map_add, encodedRotation_first_zero, zero_add, radialGaugeDecodedKernel,
    fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
  abel

theorem radialThirdForceTrace_split (angular cell : ℕ)
    (encoded known : NegativeTrace (rp parameters r) angular cell 3)
    (xiZeta : NegativeTrace (rp parameters r) angular cell 1) :
    radialThirdForceTrace parameters L compact state r small angular cell encoded known xiZeta =
    radialEncodedRowTwo parameters L compact state r small angular cell encoded +
    forceMeanFreeTrace (rp parameters r) angular cell
      (fullNegativeKernelAction (rp parameters r) angular cell (radialForceKernel parameters L compact state r 1 0)
        (fullNegativeKernelAction (rp parameters r) angular cell (radialGaugeQKernel parameters L compact state r small) known)) -
    (L : ℂ)⁻¹ • xiZeta := by
  unfold radialThirdForceTrace radialEncodedRowTwo
  rw [radialForceChart_split, map_add, map_add]
  abel

/-- Full AE12/AE19 equivalence in its three scalar coordinates. The first
row uses its genuine derivative and its mean, so no periodic condition is lost. -/
theorem radialForceEncoding_iff (angular cell : ℕ)
    (encoded known knownDerivative : NegativeTrace (rp parameters r) angular cell 3)
    (xiZeta sourceZero sourceDerivative sourceTwo : NegativeTrace (rp parameters r) angular cell 1)
    (supported : EncodedSupport (rp parameters r) angular cell encoded)
    (knownMean : IsAngularMeanFreeComponent (rp parameters r) angular cell 0 known)
    (knownLaw : IsAngularDerivative (rp parameters r) angular cell known knownDerivative)
    (sourceLaw : IsAngularDerivative (rp parameters r) angular cell sourceZero sourceDerivative) :
    (radialFirstForceTrace parameters L compact state r small angular cell encoded known = sourceZero ∧
     radialThirdForceTrace parameters L compact state r small angular cell encoded known xiZeta = sourceTwo) ↔
    (radialEncodedRowZero parameters L compact state r small angular cell encoded =
      radialForceDataZero parameters L compact state r small angular cell known sourceZero ∧
     radialEncodedRowOne parameters L compact state r small angular cell encoded =
      radialForceDataOne parameters L compact state r small angular cell known knownDerivative sourceDerivative ∧
     radialEncodedRowTwo parameters L compact state r small angular cell encoded =
      radialForceDataTwo parameters L compact state r small angular cell known xiZeta sourceTwo) := by
  rw [radialFirstForceTrace_iff parameters L compact state r small angular cell encoded known knownDerivative
    sourceZero sourceDerivative supported knownLaw sourceLaw,
    radialFirstForceTrace_mean_split parameters L compact state r small angular cell encoded known supported knownMean,
    radialFirstForceDerivativeTrace_split parameters L compact state r small angular cell encoded known knownDerivative knownLaw,
    radialThirdForceTrace_split]
  unfold radialForceDataZero radialForceDataOne radialForceDataTwo
  constructor
  · rintro ⟨⟨hzero, hone⟩, htwo⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [← hzero]
      abel
    · rw [← hone]
      abel
    · rw [← htwo]
      abel
  · rintro ⟨hzero, hone, htwo⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hzero]
      abel
    · rw [hone]
      abel
    · rw [htwo]
      abel

end Grad.AnnularReconstruction
