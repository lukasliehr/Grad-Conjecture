import AJA3ActualBulkFormOrbit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.AnnularHighInverseOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularKernelL2 Grad.AnnularCurrentEnergy
open Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule

section Inner
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem orbitLp_inner_move (tau : OrbitParameter) (first second : lp (fun _ : ℤ × ℤ => E) 2) :
    inner ℂ first (orbitLpAction E tau second) = inner ℂ (orbitLpAction E (-tau) first) second := by
  have translated := (orbitLpEquivalence E (-tau)).inner_map_map first (orbitLpAction E tau second)
  change inner ℂ (orbitLpAction E (-tau) first)
    (orbitLpAction E (-tau) (orbitLpAction E tau second)) = inner ℂ first (orbitLpAction E tau second) at translated
  have inverse := orbitLpAction_inverse E (-tau) second
  simp only [neg_neg] at inverse
  rw [inverse] at translated
  exact translated.symm

end Inner

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)

/-- Exact original bulk-form pullback by the genuine energy translations. -/
theorem highBulkFormOrbit_pullback (tau : OrbitParameter) (field test : annularEnergySpace lower L positive) :
    highBulkFormOrbit parameters L lower positive lengthPositive widthHalf widthLength compact bounded state tau field test =
      currentHighBulkForm parameters L compact lower positive bounded lengthPositive widthHalf widthLength state 0
        (energyTranslation lower L positive (-tau) field) (energyTranslation lower L positive (-tau) test) := by
  change highBulkPairing parameters L lower positive lengthPositive widthHalf widthLength
    (actualEliminatedOrbit parameters L compact lower positive bounded state 0 tau) field test = _
  rw [highBulkPairing_literal, currentHighBulkForm_literal]
  unfold currentHighBulkFormValue
  rw [actualEliminatedOrbit_conjugation]
  simp only [ContinuousLinearMap.comp_apply]
  rw [orbitLp_inner_move]
  rw [← highEnergyTestPacket_translation lower L positive parameters lengthPositive widthHalf widthLength (-tau) test,
    ← highEightEnergyPacket_translation lower L positive parameters lengthPositive widthHalf widthLength (-tau) field]

/-- Every positive mixed bulk-form jet costs only one high primitive moment. -/
theorem highBulkFormOrbitJet_oneHigh (angular cell : ℕ) (orderPositive : 0 < angular + cell) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < L)
        (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
        (state : RetainedInverseState parameters L compact) (tau : OrbitParameter),
      ‖highBulkFormOrbitJet parameters L lower positive lengthPositive widthHalf widthLength compact bounded state tau angular cell‖ ≤
        constant * state.val.errorBudget (angular + cell) := by
  obtain ⟨constant, nonnegative, bound⟩ := actualEliminatedOrbitJet_oneHigh parameters L compact 0 angular cell orderPositive
  refine ⟨5 * (4 + 2 * |L|) * constant, by positivity, ?_⟩
  intro lower positive bounded lengthPositive widthHalf widthLength state tau
  have estimate := highBulkPairing_norm_bound parameters L lower positive lengthPositive widthHalf widthLength
    (actualEliminatedOrbitJet parameters L compact lower positive bounded state 0 tau angular cell)
  have actual := bound state lower positive bounded tau
  change ‖highBulkPairing parameters L lower positive lengthPositive widthHalf widthLength
    (actualEliminatedOrbitJet parameters L compact lower positive bounded state 0 tau angular cell)‖ ≤ _
  simp only [zero_add] at actual
  exact estimate.trans ((mul_le_mul_of_nonneg_left actual (by positivity : 0 ≤ 5 * (4 + 2 * |L|))).trans_eq (by ring))

end Grad.AnnularHighInverseOrbit
