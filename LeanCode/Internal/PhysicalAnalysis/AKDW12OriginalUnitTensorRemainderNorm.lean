import AKDW10OriginalUnitNativeFluxEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxRecDepth 4000
open Set
open scoped ContDiff
namespace Grad.OriginalCoreRealization.OriginalUnitRankState
open Grad.ClosedJets Grad.CartesianState Grad.CartesianStartup Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.SourceCollarCoefficients Grad.NonlinearProduct Grad.TensorBootstrap
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.RadialLedger

/-- The actual physical-L principal controls the genuine L2 second tensor
remainder at arbitrary epsilon, with the known tensor paid at its own rank. -/
theorem compactTensor_remainder_bound (parameters : PhaseParameters) (length radius : ℝ)
    (radiusNonnegative : 0≤radius) (rank : ℕ) (index : TensorIndex)
    {inside : Set Spatial} (closed : IsClosed inside)
    (outer : Spatial → ℝ) (smooth : ContDiff ℝ ∞ outer) (compact : HasCompactSupport outer)
    (plateau : ∀ point∈inside,outer point=1) (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ constant : ℝ,0≤constant ∧ ∀ (state : OriginalUnitRankState parameters length radius)
      (core principal known : ACore parameters 3) (data : StartupCompactSpatialEquation rank inside),
      base 3 rank openUnitDisk (fun _ => 0) data.field=originalSourceFieldLinear parameters core →
      base 3 rank openUnitDisk (fun _ => 0) (data.tensor index.1 index.2)=originalSourceFieldLinear parameters (principal+known) →
      originalSourceFieldLinear parameters principal=
        startupGenuinePrincipalTensorKernel (unitDiskAdmissible parameters) state.data
          (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative) index.1 index.2
          (originalSourceFieldLinear parameters core) →
      ‖startupActualRankTensorRemainder data outer smooth compact
        (fun first second => StartupRankOperator.principalTensor (unitDiskAdmissible parameters) rank state.data
          (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative) first second) index‖≤
      epsilon*originalGradeNorm rank core+constant*(originalGradeNorm rank known+budget rank state*originalGradeNorm 0 core) := by
  let endpoint := principal_endpoint parameters length radius radiusNonnegative rank index.1 index.2
  let profile := endpoint.1.choose
  let delta := epsilon/(‖startupCutoffL2 outer smooth compact‖+1)
  have deltaPositive : 0<delta := div_pos positive (by positivity)
  let tail := profile.remainder delta
  have tailNonnegative : 0≤tail := profile.remainderNonnegative delta deltaPositive
  refine ⟨‖startupCutoffL2 outer smooth compact‖*(tail+(Fintype.card (CartesianWord rank) : ℝ)),
    mul_nonneg (norm_nonneg _) (add_nonneg tailNonnegative (Nat.cast_nonneg _)),?_⟩
  intro state core principal known data fieldSame tensorSame principalSame
  let actual := (endpoint.1.choose_spec state).some
  have imageSame : principal=actual.action core := originalSourceFieldLinear_injective parameters
    (principalSame.trans (actual.same core).symm)
  have allocated : ‖startupCutoffL2 outer smooth compact‖*delta≤epsilon := by
    have exactDelta : delta*(‖startupCutoffL2 outer smooth compact‖+1)=epsilon := div_mul_cancel₀ epsilon (by positivity)
    nlinarith [deltaPositive]
  apply startupCompactTensorRemainder_bound parameters rank index closed outer smooth compact plateau _
    core principal known data fieldSame tensorSame epsilon delta tail (budget rank state)
    tailNonnegative (budget_nonnegative rank state) allocated
  rw [imageSame]
  exact actual.remainderBound delta deltaPositive core

end Grad.OriginalCoreRealization.OriginalUnitRankState
