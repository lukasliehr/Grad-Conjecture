import GQC14APUnweightedSmooth

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.AnalyticWeights.Calculus
open Grad.GaugeCoefficients.Envelope

theorem apWeightedMultiDerivative_zero {dimension grade : ℕ} (L sigma gamma ell : ℝ)
    (large : 2 ≤ grade) (cell : ℤ) (field : apGrade L sigma gamma ell dimension grade) :
    apWeightedMultiDerivative L sigma gamma ell (0, 0) large cell field = apWeightedTrace L sigma gamma ell large cell field := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := dimension) (grade := grade) L sigma gamma ell)
    (isClosed_eq (apWeightedMultiDerivative L sigma gamma ell (0, 0) large cell).continuous
      (apWeightedTrace L sigma gamma ell large cell).continuous) _ field
  intro core
  rw [apWeightedMultiDerivative_core L sigma gamma ell (0, 0) large cell core,
    apWeightedTrace_core, closedMultiDerivative_zero]

theorem apFamilyWeightedJet_value_trace {L sigma gamma ell : ℝ} {dimension grade : ℕ}
    (family : APFamily L sigma gamma ell dimension) (coherent : APFamilyCoherent family)
    (large : 2 ≤ grade) (cell : ℤ) :
    (apFamilyWeightedJet family coherent cell).value = apWeightedTrace L sigma gamma ell large cell (family grade) := by
  change apFamilyClosedDerivative family cell (0, 0) = _
  rw [apFamilyClosedDerivative_eq family coherent cell (0, 0) large, apWeightedMultiDerivative_zero]

theorem apFamilyJet_value_trace {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension grade : ℕ} (family : APFamily L sigma gamma ell dimension) (coherent : APFamilyCoherent family)
    (large : 2 ≤ grade) (cell : ℤ) :
    (apFamilyJet family coherent cell).value = apTrace admissible large cell (family grade) := by
  apply ContinuousMap.ext
  intro point
  change inverseWeight sigma gamma ell cell point.val • (apFamilyWeightedJet family coherent cell).value point =
    (originalWeight sigma gamma ell cell point.val)⁻¹ • (apWeightedTrace L sigma gamma ell large cell (family grade)) point
  rw [apFamilyWeightedJet_value_trace family coherent large cell]
  rfl

theorem apFamilyJet_add {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (first second : APFamily L sigma gamma ell dimension)
    (firstCoherent : APFamilyCoherent first) (secondCoherent : APFamilyCoherent second)
    (sumCoherent : APFamilyCoherent (first + second)) (cell : ℤ) :
    apFamilyJet (first + second) sumCoherent cell = apFamilyJet first firstCoherent cell + apFamilyJet second secondCoherent cell := by
  apply closedJet_eq_of_value_eq
  change (apFamilyJet (first + second) sumCoherent cell).value =
    (apFamilyJet first firstCoherent cell).value + (apFamilyJet second secondCoherent cell).value
  rw [apFamilyJet_value_trace admissible _ sumCoherent (by omega : 2 ≤ 2),
    apFamilyJet_value_trace admissible first firstCoherent (by omega : 2 ≤ 2),
    apFamilyJet_value_trace admissible second secondCoherent (by omega : 2 ≤ 2)]
  exact (apTrace admissible (by omega : 2 ≤ 2) cell).map_add (first 2) (second 2)

theorem apFamilyJet_smul {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (scalar : ℂ) (family : APFamily L sigma gamma ell dimension)
    (coherent : APFamilyCoherent family) (scaledCoherent : APFamilyCoherent (scalar • family)) (cell : ℤ) :
    apFamilyJet (scalar • family) scaledCoherent cell = scalar • apFamilyJet family coherent cell := by
  apply closedJet_eq_of_value_eq
  change (apFamilyJet (scalar • family) scaledCoherent cell).value = scalar • (apFamilyJet family coherent cell).value
  rw [apFamilyJet_value_trace admissible _ scaledCoherent (by omega : 2 ≤ 2),
    apFamilyJet_value_trace admissible family coherent (by omega : 2 ≤ 2)]
  exact (apTrace admissible (by omega : 2 ≤ 2) cell).map_smul scalar (family 2)

end Grad.GaugeCoefficients.Physical.Compensated
