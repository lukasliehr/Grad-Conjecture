import ANP3SignedDerivativeCovariance
import GQF44ActualConsumer
import AXF22SpinMaps

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.RawCircularSectors
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.FlatSourceProjection

/-- Literal raw angular sector: the two Cartesian helicities carry m+1 and m-1. -/
def rawVectorJetLinear (mode : ℤ) : ClosedJet 2 →ₗ[ℂ] ClosedJet 2 :=
  (valueMapJetLinear 2 2 positiveHelicity).comp (angularClosedJetLinear 2 (mode + 1)) +
    (valueMapJetLinear 2 2 negativeHelicity).comp (angularClosedJetLinear 2 (mode - 1))

def rawVectorJet (mode : ℤ) (field : ClosedJet 2) : ClosedJet 2 := rawVectorJetLinear mode field

theorem rawVectorJet_eq (mode : ℤ) (field : ClosedJet 2) :
    rawVectorJet mode field = valueMapJet positiveHelicity (angularClosedJet (mode + 1) field) +
      valueMapJet negativeHelicity (angularClosedJet (mode - 1) field) := rfl

theorem rawVectorJet_zero (field : ClosedJet 2) : rawVectorJet 0 field = equivariantAverageJet field := by
  simp only [rawVectorJet_eq, zero_add, zero_sub, equivariantAverageJet_eq]

theorem rawVectorJet_projection (first second : ℤ) (field : ClosedJet 2) :
    rawVectorJet first (rawVectorJet second field) =
      if first = second then rawVectorJet first field else 0 := by
  simp only [rawVectorJet_eq, angularClosedJet_add, angularClosedJet_valueMap,
    valueMapJet_add, valueMapJet_comp, positiveHelicity_idempotent, negativeHelicity_idempotent,
    positiveHelicity_negative, negativeHelicity_positive, valueMapJet_zero, add_zero, zero_add]
  rw [angularClosedJet_projection, angularClosedJet_projection]
  by_cases same : first = second
  · subst second
    simp
  · have positive : first + 1 ≠ second + 1 := by omega
    have negative : first - 1 ≠ second - 1 := by omega
    simp [same, positive, negative, valueMapJet_map_zero]

/-- Exact scalar spin consequence, using the existing AXF physical spin map. -/
theorem rawVectorJet_spin (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (mode : ℤ) (field : ClosedJet 2) :
    valueMapJet (spinValue (sign : ℂ)) (rawVectorJet mode field) =
      angularClosedJet (mode + sign) (valueMapJet (spinValue (sign : ℂ)) field) := by
  rcases signed with rfl | rfl
  · simp only [Int.cast_one, rawVectorJet_eq, valueMapJet_add, valueMapJet_comp,
      spinValue_positive, spinValue_negative_zero, valueMapJet_zero, add_zero]
    exact (angularClosedJet_valueMap (spinValue 1) (mode + 1) field).symm
  · simp only [Int.cast_neg, Int.cast_one, rawVectorJet_eq, valueMapJet_add, valueMapJet_comp,
      spinValue_positive_zero, spinValue_negative, valueMapJet_zero, zero_add]
    simpa only [sub_eq_add_neg] using (angularClosedJet_valueMap (spinValue (-1)) (mode - 1) field).symm

theorem rawVectorSector_spin (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (mode : ℤ) (field : ClosedJet 2)
    (pure : rawVectorJet mode field = field) :
    angularClosedJet (mode + sign) (valueMapJet (spinValue (sign : ℂ)) field) =
      valueMapJet (spinValue (sign : ℂ)) field :=
  (rawVectorJet_spin sign signed mode field).symm.trans (congrArg (valueMapJet (spinValue (sign : ℂ))) pure)

variable {L sigma gamma ell : ℝ}

def apSmoothRawVector (L sigma gamma ell : ℝ) (mode : ℤ) :
    APSmooth L sigma gamma ell 2 →ₗ[ℂ] APSmooth L sigma gamma ell 2 :=
  (apSmoothValueMap L sigma gamma ell positiveHelicity).comp
    (apSmoothAngularMode L sigma gamma ell 2 (mode + 1)) +
  (apSmoothValueMap L sigma gamma ell negativeHelicity).comp
    (apSmoothAngularMode L sigma gamma ell 2 (mode - 1))

theorem apSmoothRawVector_jet (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (field : APSmooth L sigma gamma ell 2) (cell : ℤ) :
    apSmoothJet admissible 2 cell (apSmoothRawVector L sigma gamma ell mode field) =
      rawVectorJet mode (apSmoothJet admissible 2 cell field) := by
  have positive := (apSmoothValueMap_jet admissible positiveHelicity
    (apSmoothAngularMode L sigma gamma ell 2 (mode + 1) field) cell).trans
      (congrArg (valueMapJet positiveHelicity) (apSmoothAngularMode_jet admissible (mode + 1) field cell))
  have negative := (apSmoothValueMap_jet admissible negativeHelicity
    (apSmoothAngularMode L sigma gamma ell 2 (mode - 1) field) cell).trans
      (congrArg (valueMapJet negativeHelicity) (apSmoothAngularMode_jet admissible (mode - 1) field cell))
  exact (map_add (apSmoothJet admissible 2 cell) _ _).trans
    (congrArg₂ (fun first second : ClosedJet 2 => first + second) positive negative)

/-- Original smooth source carrier, with literal raw sector at every cell. -/
def IsRawSourceSector (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (source : SmoothCapSource L sigma gamma ell) : Prop :=
  (∀ cell, rawVectorJet mode (apSmoothJet admissible 2 cell source.1) = apSmoothJet admissible 2 cell source.1) ∧
  (∀ cell, angularClosedJet mode (apSmoothJet admissible 1 cell source.2.1) = apSmoothJet admissible 1 cell source.2.1) ∧
  (∀ cell, angularClosedJet mode (apSmoothJet admissible 1 cell source.2.2) = apSmoothJet admissible 1 cell source.2.2)

/-- Original compensated coordinates, with scalar and vector raw sectors. -/
def IsRawStateSector (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (state : CompensatedData L sigma gamma ell) : Prop :=
  (∀ cell, angularClosedJet mode (apSmoothJet admissible 1 cell state.1) = apSmoothJet admissible 1 cell state.1) ∧
  (∀ cell, rawVectorJet mode (apSmoothJet admissible 2 cell (apSmoothPlanar L sigma gamma ell state.2)) =
    apSmoothJet admissible 2 cell (apSmoothPlanar L sigma gamma ell state.2)) ∧
  (∀ cell, angularClosedJet mode (apSmoothJet admissible 1 cell (apSmoothScalar L sigma gamma ell state.2)) =
    apSmoothJet admissible 1 cell (apSmoothScalar L sigma gamma ell state.2))

theorem rawSourceSector_spin (admissible : Admissible L sigma gamma ell) (mode sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (pure : IsRawSourceSector admissible mode source) (cell : ℤ) :
    angularClosedJet (mode + sign) (valueMapJet (spinValue (sign : ℂ)) (apSmoothJet admissible 2 cell source.1)) =
      valueMapJet (spinValue (sign : ℂ)) (apSmoothJet admissible 2 cell source.1) :=
  rawVectorSector_spin sign signed mode _ (pure.1 cell)

end Grad.RawCircularSectors
