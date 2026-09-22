import AKN19SameFullG3AngularBound
import ANR26OrdinaryRadialPairing
import ASG22WeakGraphConverse

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Grad.ExhaustionSourceAllocation
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularSourceGraph
open Grad.CircularHighRegularity Grad.GaugeCoefficients.Physical.WeightedTrace

theorem radialSqrtMap_ordinary (dimension : ℕ) (lower : ℝ) (positive : 0 < lower)
    (field : RadialL2 dimension lower) :
    radialSqrtMap dimension lower (radialOrdinary dimension lower positive field) = field := by
  apply Lp.ext
  filter_upwards [radialSqrtMap_ae dimension lower (radialOrdinary dimension lower positive field),
    radialOrdinary_ae dimension lower positive field, ae_restrict_mem measurableSet_Icc]
    with radius stored decoded inside
  rw [stored, decoded, smul_smul, reciprocalRadialWeight, max_eq_right inside.1,
    one_div, mul_inv_cancel₀ (Real.sqrt_pos.2 (positive.trans_le inside.1)).ne', one_smul]

/-- Decode the accepted source radial graph into the same ordinary weak derivative.
The sqrt(r) storage is removed on both coordinates. -/
theorem sourceWeakDerivative_ordinary (dimension : ℕ) (lower : ℝ) (positive : 0 < lower)
    (value derivative : RadialL2 dimension lower)
    (weak : HasWeakRadialDerivative lower positive value derivative) :
    CollarWeakDerivative lower (radialOrdinary dimension lower positive value)
      (radialOrdinary dimension lower positive derivative) := by
  intro test vector
  let sourceTest : RadialTest lower :=
    ⟨test.value, test.derivative, test.value.continuous, test.derivative.continuous,
      test.derivativeLaw, test.lowerZero, test.upperZero⟩
  simpa only [sourceTest, radialPairing_ordinary] using weak sourceTest vector

/-- Every accepted source derivative pair lies in the original smooth weighted
radial completion, with exactly its original stored coordinates. -/
theorem sourceWeakPair_realization (dimension : ℕ) (lower : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (value derivative : RadialL2 dimension lower)
    (weak : HasWeakRadialDerivative lower positive value derivative) :
    ∃ field : WeightedRadialH1 dimension lower,
      weightedRadialCoordinate dimension lower 0 field = value ∧
      weightedRadialCoordinate dimension lower 1 field = derivative := by
  obtain ⟨field, first, second⟩ := weakPair_weighted_coordinates dimension lower positive bounded
    (radialOrdinary dimension lower positive value) (radialOrdinary dimension lower positive derivative)
    (sourceWeakDerivative_ordinary dimension lower positive value derivative weak)
  exact ⟨field, first.trans (radialSqrtMap_ordinary dimension lower positive value),
    second.trans (radialSqrtMap_ordinary dimension lower positive derivative)⟩

end Grad.ExhaustionSourceAllocation
