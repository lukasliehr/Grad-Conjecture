import AJB27OriginalLowGradeNormBound
import AJB30IndependentLowDataGenerators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.AnnularLowOrbit
open Grad.AnnularLowEnergy Grad.AnnularLowCompletion Grad.AnnularVariational

/-- All four actual low angular modes are retained in the BF frequency. -/
theorem lowInsertedFrequency_power_bound (grade : ℕ) (index : LowAnnularIndex) :
    |lowInsertedFrequency index ^ grade| ≤ ((3 : ℝ) ^ grade * (2 : ℝ) ^ grade) *
      (1 + |(index.2.val.2 : ℝ)| ^ grade) := by
  have angularInt : |index.2.val.1| ≤ 2 := by rcases index.2.property with one | two <;> omega
  have angularReal : |(index.2.val.1 : ℝ)| ≤ 2 := by exact_mod_cast angularInt
  have frequency : lowInsertedFrequency index ≤ 3 * (1 + |(index.2.val.2 : ℝ)|) := by
    unfold lowInsertedFrequency annularFrequency
    nlinarith only [angularReal, abs_nonneg (index.2.val.2 : ℝ)]
  rw [abs_of_nonneg (pow_nonneg (lowInsertedFrequency_positive index).le grade)]
  have first := pow_le_pow_left₀ (lowInsertedFrequency_positive index).le frequency grade
  rw [mul_pow] at first
  have sum := Grad.BoundaryTrace.two_term_pow_bound 1 |(index.2.val.2 : ℝ)| zero_le_one (abs_nonneg _) grade
  simp only [one_pow] at sum
  exact first.trans ((mul_le_mul_of_nonneg_left sum (by positivity : 0 ≤ (3 : ℝ) ^ grade)).trans_eq (by ring))

/-- The literal BF insertion belongs to the genuine original graph whenever
the complete cell generator exists. Its radius-uniform norm is explicit. -/
theorem lowGraph_insertedGrade_of_generator (lower length : ℝ) (positive : 0 < lower)
    (field generator : lowEnergyGraph lower length positive) (grade : ℕ)
    (actual : ∀ (coordinate : Fin 2) (index : LowAnnularIndex),
      generator.val coordinate index = (Complex.I * (index.2.val.2 : ℂ)) ^ grade • field.val coordinate index) :
    ∃ weighted : lowEnergyGraph lower length positive,
      (∀ (coordinate : Fin 2) (index : LowAnnularIndex), weighted.val coordinate index =
        ((lowInsertedFrequency index ^ grade : ℝ) : ℂ) • field.val coordinate index) ∧
      ‖weighted‖ ≤ 2 * ((3 : ℝ) ^ grade * (2 : ℝ) ^ grade) * (‖field‖ + ‖generator‖) := by
  let constant := (3 : ℝ) ^ grade * (2 : ℝ) ^ grade
  have nonnegative : 0 ≤ constant := by positivity
  have membership (coordinate : Fin 2) :
      Memℓp (fun index => ((lowInsertedFrequency index ^ grade : ℝ) : ℂ) • field.val coordinate index) 2 :=
    lowWeighted_memℓp_of_generator lower (field.val coordinate) (generator.val coordinate) grade (actual coordinate)
      (fun index => lowInsertedFrequency index ^ grade) constant nonnegative (lowInsertedFrequency_power_bound grade)
  let weighted := lowSummableGraphMultiplier lower length positive field
    (fun index => ((lowInsertedFrequency index ^ grade : ℝ) : ℂ)) membership
  refine ⟨weighted, fun _ _ => rfl, ?_⟩
  let bound := constant * (‖field‖ + ‖generator‖)
  have boundNonnegative : 0 ≤ bound := mul_nonneg nonnegative (add_nonneg (norm_nonneg _) (norm_nonneg _))
  have coordinateBound (coordinate : Fin 2) : ‖weighted.val coordinate‖ ≤ bound := by
    have estimate := lowWeighted_bulk_norm_bound lower (field.val coordinate) (generator.val coordinate)
      (weighted.val coordinate) grade (actual coordinate) (fun index => lowInsertedFrequency index ^ grade)
      (fun _ => rfl) constant nonnegative (lowInsertedFrequency_power_bound grade)
    exact estimate.trans (mul_le_mul_of_nonneg_left
      (add_le_add (lowStoredCoordinate_bound lower length positive coordinate field)
        (lowStoredCoordinate_bound lower length positive coordinate generator)) nonnegative)
  have squared := lowEnergyGraph_norm_sq lower length positive weighted
  have first := pow_le_pow_left₀ (norm_nonneg _) (coordinateBound 0) 2
  have second := pow_le_pow_left₀ (norm_nonneg _) (coordinateBound 1) 2
  have final : ‖weighted‖ ≤ 2 * bound := by
    nlinarith only [squared, first, second, boundNonnegative, norm_nonneg weighted, sq_nonneg bound]
  exact final.trans_eq (by dsimp [bound, constant]; ring)

end Grad.AnnularLowOrbit
