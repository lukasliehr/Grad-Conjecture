import GQC28APAxial

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Ledger

theorem apFixedJet_trace {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output grade : ℕ} (large : 2 ≤ grade) (coefficient : SmoothOperatorJet input output)
    (field : apGrade L sigma gamma ell input grade) (cell : ℤ) (point : ClosedDisk) :
    apTrace admissible large cell (apMultiplier admissible (fixedJetFamily L sigma gamma ell coefficient grade) field) point =
      coefficient.value point (apTrace admissible large cell field point) := by
  let first := (ContinuousMap.evalCLM ℂ point).comp ((apTrace admissible large cell).comp
    (apMultiplier admissible (singleJetCoefficient L sigma gamma ell grade 0 coefficient)))
  let second := (coefficient.value point).comp ((ContinuousMap.evalCLM ℂ point).comp (apTrace admissible large cell))
  have equality : first = second := by
    apply apFiniteGenerator_ext L sigma gamma ell first second
    intro inputCell core
    change apTrace admissible large cell
      (apMultiplier admissible (singleJetCoefficient L sigma gamma ell grade 0 coefficient)
        (apFiniteInto L sigma gamma ell (Finsupp.single inputCell core))) point =
      coefficient.value point (apTrace admissible large cell (apFiniteInto L sigma gamma ell (Finsupp.single inputCell core)) point)
    rw [apMultiplier_single, add_zero, apTrace_core, apTrace_core]
    by_cases same : cell = inputCell
    · subst cell
      rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
      exact apProductJet_value coefficient core point
    · rw [Finsupp.single_eq_of_ne same, Finsupp.single_eq_of_ne same]
      change (0 : ComplexEuclidean output) = coefficient.value point 0
      exact (map_zero _).symm
  change first field = second field
  rw [equality]

def apSmoothFixedJet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (coefficient : SmoothOperatorJet input output) :
    APSmooth L sigma gamma ell input →ₗ[ℂ] APSmooth L sigma gamma ell output :=
  apSmoothMultiplier admissible (fixedJetFamily L sigma gamma ell coefficient) (fixedJetFamily_coherent L sigma gamma ell coefficient)

theorem apSmoothFixedJet_jet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (coefficient : SmoothOperatorJet input output)
    (field : APSmooth L sigma gamma ell input) (cell : ℤ) :
    apSmoothJet admissible output cell (apSmoothFixedJet admissible coefficient field) =
      apProductJet coefficient (apSmoothJet admissible input cell field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [apProductJet_value]
  change (apFamilyJet (apSmoothFixedJet admissible coefficient field).val _ cell).value point =
    coefficient.value point ((apFamilyJet field.val field.property cell).value point)
  rw [apFamilyJet_value_trace admissible (apSmoothFixedJet admissible coefficient field).val
    (apSmoothFixedJet admissible coefficient field).property (by omega : 2 ≤ 2) cell,
    apFamilyJet_value_trace admissible field.val field.property (by omega : 2 ≤ 2) cell]
  exact apFixedJet_trace admissible (by omega : 2 ≤ 2) coefficient (field.val 2) cell point

theorem apProductJet_coordinate {dimension : ℕ} (coordinate : Fin 2) (field : ClosedJet dimension) :
    apProductJet (coordinateOperatorJet coordinate (ContinuousLinearMap.id ℂ (ComplexEuclidean dimension))) field =
      Grad.NonlinearQuotientBounds.coordinateJet coordinate field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [apProductJet_value, coordinateOperatorJet_value, Grad.NonlinearQuotientBounds.coordinateJet_value]
  exact Complex.coe_smul (point.val coordinate) (field.value point)

def apSmoothCoordinate {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (dimension : ℕ) (coordinate : Fin 2) : APSmooth L sigma gamma ell dimension →ₗ[ℂ] APSmooth L sigma gamma ell dimension :=
  apSmoothFixedJet admissible (coordinateOperatorJet coordinate (ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)))

theorem apSmoothCoordinate_jet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (coordinate : Fin 2) (field : APSmooth L sigma gamma ell dimension) (cell : ℤ) :
    apSmoothJet admissible dimension cell (apSmoothCoordinate admissible dimension coordinate field) =
      Grad.NonlinearQuotientBounds.coordinateJet coordinate (apSmoothJet admissible dimension cell field) := by
  rw [show apSmoothCoordinate admissible dimension coordinate = apSmoothFixedJet admissible
    (coordinateOperatorJet coordinate (ContinuousLinearMap.id ℂ (ComplexEuclidean dimension))) from rfl, apSmoothFixedJet_jet]
  exact apProductJet_coordinate coordinate _

end Grad.GaugeCoefficients.Physical.Compensated
