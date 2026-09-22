import AJF4ActualHighAxisGenerators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped ContDiff
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularOmegaGraph Grad.AnnularCoupledOrbit
open Grad.AnnularKernelOrbit Grad.AnnularInverseCalculus Grad.AnnularOrbitGenerators

/-- Literal nu insertion in the original completed W, controlled by the
actual angular and cell generators with a radius-independent constant. -/
theorem energy_insertedGrade_of_generators (lower length : ℝ) (positive : 0 < lower)
    (field angular cell : annularEnergySpace lower length positive) (grade : ℕ)
    (angularActual : ∀ index : HighAnnularMode,
      angular.val index = (Complex.I * (index.val.1 : ℂ)) ^ grade • field.val index)
    (cellActual : ∀ index : HighAnnularMode,
      cell.val index = (Complex.I * (index.val.2 : ℂ)) ^ grade • field.val index) :
    ∃ weighted : annularEnergySpace lower length positive,
      (∀ index : HighAnnularMode, weighted.val index =
        ((annularFrequency index.val.1 index.val.2 ^ grade : ℝ) : ℂ) • field.val index) ∧
      ‖weighted‖ ≤ (4 : ℝ) ^ grade * (‖field‖ + ‖angular‖ + ‖cell‖) := by
  have membership := twoGenerator_weighted_memℓp field.val angular.val cell.val
    (fun index : HighAnnularMode => index.val.1) (fun index : HighAnnularMode => index.val.2)
    grade angularActual cellActual (fun index => annularFrequency index.val.1 index.val.2 ^ grade)
    (4 ^ grade) (by positivity) (fun index => highFrequency_power_bound grade index.val)
  let weighted := energySummableMultiplier lower length positive field
    (fun index => ((annularFrequency index.val.1 index.val.2 ^ grade : ℝ) : ℂ)) membership
  refine ⟨weighted, fun _ => rfl, ?_⟩
  exact twoGenerator_weighted_norm field.val angular.val cell.val weighted.val
    (fun index : HighAnnularMode => index.val.1) (fun index : HighAnnularMode => index.val.2)
    grade angularActual cellActual (fun index => annularFrequency index.val.1 index.val.2 ^ grade)
    (fun _ => rfl) (4 ^ grade) (by positivity) (fun index => highFrequency_power_bound grade index.val)

/-- The same insertion lies in the literal Domega graph, on both stored
coordinates, with no separately prescribed derivative or trace. -/
theorem flux_insertedGrade_of_generators (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field angular cell : annularOmegaGraph lower length positive lengthPositive) (grade : ℕ)
    (angularActual : ∀ (coordinate : Fin 2) (index : HighAnnularMode),
      angular.val coordinate index = (Complex.I * (index.val.1 : ℂ)) ^ grade • field.val coordinate index)
    (cellActual : ∀ (coordinate : Fin 2) (index : HighAnnularMode),
      cell.val coordinate index = (Complex.I * (index.val.2 : ℂ)) ^ grade • field.val coordinate index) :
    ∃ weighted : annularOmegaGraph lower length positive lengthPositive,
      (∀ (coordinate : Fin 2) (index : HighAnnularMode), weighted.val coordinate index =
        ((annularFrequency index.val.1 index.val.2 ^ grade : ℝ) : ℂ) • field.val coordinate index) ∧
      ‖weighted‖ ≤ 2 * (4 : ℝ) ^ grade * (‖field‖ + ‖angular‖ + ‖cell‖) := by
  have membership (coordinate : Fin 2) := twoGenerator_weighted_memℓp
    (field.val coordinate) (angular.val coordinate) (cell.val coordinate)
    (fun index : HighAnnularMode => index.val.1) (fun index : HighAnnularMode => index.val.2)
    grade (angularActual coordinate) (cellActual coordinate) (fun index => annularFrequency index.val.1 index.val.2 ^ grade)
    (4 ^ grade) (by positivity) (fun index => highFrequency_power_bound grade index.val)
  let weighted := fluxSummableMultiplier lower length positive lengthPositive field
    (fun index => ((annularFrequency index.val.1 index.val.2 ^ grade : ℝ) : ℂ)) membership
  refine ⟨weighted, fun _ _ => rfl, ?_⟩
  let bound := (4 : ℝ) ^ grade * (‖field‖ + ‖angular‖ + ‖cell‖)
  have nonnegative : 0 ≤ bound := by dsimp [bound]; positivity
  have coordinateBound (coordinate : Fin 2) : ‖weighted.val coordinate‖ ≤ bound := by
    have estimate := twoGenerator_weighted_norm
      (field.val coordinate) (angular.val coordinate) (cell.val coordinate) (weighted.val coordinate)
      (fun index : HighAnnularMode => index.val.1) (fun index : HighAnnularMode => index.val.2)
      grade (angularActual coordinate) (cellActual coordinate) (fun index => annularFrequency index.val.1 index.val.2 ^ grade)
      (fun _ => rfl) (4 ^ grade) (by positivity) (fun index => highFrequency_power_bound grade index.val)
    exact estimate.trans (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add
        (fluxStoredCoordinate_bound lower length positive lengthPositive coordinate field)
        (fluxStoredCoordinate_bound lower length positive lengthPositive coordinate angular))
        (fluxStoredCoordinate_bound lower length positive lengthPositive coordinate cell)) (by positivity))
  have squared := annularOmegaGraph_norm_sq lower length positive lengthPositive weighted
  have first := pow_le_pow_left₀ (norm_nonneg _) (coordinateBound 0) 2
  have second := pow_le_pow_left₀ (norm_nonneg _) (coordinateBound 1) 2
  have final : ‖weighted‖ ≤ 2 * bound := by
    nlinarith only [squared, first, second, nonnegative, norm_nonneg weighted, sq_nonneg bound]
  exact final.trans_eq (by dsimp [bound]; ring)

end Grad.AnnularHighGenerators
