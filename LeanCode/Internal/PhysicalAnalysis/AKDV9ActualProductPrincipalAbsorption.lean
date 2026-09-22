import AKDV8SameProductUnitRankState
import AKDS39OriginalUnitPrincipalAbsorption

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
open scoped ContDiff

namespace Grad.OriginalMainConsumer
open Grad.CartesianState Grad.Constraints Grad.Q24Realization Grad.RealFixedRanges
open Grad.PhysicalCoordinates Grad.FinitePhysicalJetLift Grad.OriginalCoreRealization
open Grad.GaugeCoefficients.Physical.Allocation Grad.OriginalInverseNeighborhood
open Grad.NashMoser.OriginalIteration Grad.NashMoser.OriginalLimit
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianStartup Grad.SourceCollarCoefficients

variable (parameters : PhaseParameters) (positive : 0 < parameters.length)
  (reference : Seed.Parameters) (inside : reference ∈ Seed.parameterDomain)
  (center : Seed.Parameters) (insideC : center ∈ Seed.parameterDomain) (zeroC : center 0=0)
  (outer : Spatial → ℝ) (smooth : ContDiff ℝ ∞ outer) (compact : HasCompactSupport outer)

/-- One actual product meets the faithful physical-L principal radius,
chosen before the state, source and rank, at the unchanged original width. -/
def actualPrincipalProduct : OriginalPhysicalProduct parameters positive reference inside center :=
  actualOriginalProductBelow parameters positive reference inside center insideC zeroC
    (originalUnitPrincipalRadius parameters parameters.length (1+‖center‖) outer smooth compact)
    (originalUnitPrincipalRadius_positive parameters parameters.length (1+‖center‖) outer smooth compact)

local notation "principalProduct" => actualPrincipalProduct parameters positive reference inside center insideC zeroC outer smooth compact

/-- The exact original field on that product is a faithful original-L
unit ledger state. No geometric, coefficient or derivative premise is added. -/
def actualPrincipalUnitState (higher : ℕ) (higherLarge : 24 ≤ higher)
    (finite : OriginalFiniteParameter) (member : finite ∈ (principalProduct).neighborhood.parameterDomain)
    (state : stateSmoothRange parameters reference inside)
    (low : stateSize parameters reference inside higher 0 state ≤ 2*(principalProduct).neighborhood.radius) :
    OriginalUnitRankState parameters parameters.length (1+‖center‖) :=
  actualProduct_unitRankState parameters positive reference inside center insideC zeroC
    (originalUnitPrincipalRadius parameters parameters.length (1+‖center‖) outer smooth compact)
    (originalUnitPrincipalRadius_positive parameters parameters.length (1+‖center‖) outer smooth compact)
    (originalUnitPrincipalRadius_le parameters parameters.length (1+‖center‖) outer smooth compact)
    higher higherLarge finite member state low

/-- The literal ordered second-tensor operator on the SAME product has
norm less than one eighth for every running rank, on a single fixed ball. -/
theorem actualPrincipalProduct_oneEighth (higher : ℕ) (higherLarge : 24 ≤ higher)
    (finite : OriginalFiniteParameter) (member : finite ∈ (principalProduct).neighborhood.parameterDomain)
    (state : stateSmoothRange parameters reference inside)
    (low : stateSize parameters reference inside higher 0 state ≤ 2*(principalProduct).neighborhood.radius)
    (rank : ℕ) :
    let unit := actualPrincipalUnitState parameters positive reference inside center insideC zeroC outer smooth compact
      higher higherLarge finite member state low
    ‖startupOrderedSecondSum rank (fun index =>
      (StartupRankOperator.principalTensor (unitDiskAdmissible parameters) rank unit.data
        (unit.coherent (by positivity)) (unit.inverseCoherent (by positivity)) index.1 index.2).localizedCoarse
        outer smooth compact)‖ < (1/8 : ℝ) := by
  let unit := actualPrincipalUnitState parameters positive reference inside center insideC zeroC outer smooth compact
    higher higherLarge finite member state low
  have radiusNonnegative : 0 ≤ 1+‖center‖ := by positivity
  apply unit.localized_principal_oneEighth radiusNonnegative outer smooth compact _ rank
  have low24 := (principalProduct).neighborhood.raiseBase_low higher higherLarge state low
  have below := actualOriginalProductBelow_budget parameters positive reference inside center insideC zeroC
    (originalUnitPrincipalRadius parameters parameters.length (1+‖center‖) outer smooth compact)
    (originalUnitPrincipalRadius_positive parameters parameters.length (1+‖center‖) outer smooth compact)
    finite member state low24
  exact (physicalBudget_monotone parameters unit.field unit.rho unit.epsilon (by norm_num : 10 ≤ 24)).trans_lt below

end Grad.OriginalMainConsumer
