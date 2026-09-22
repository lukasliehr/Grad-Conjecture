import AJF8ActualCoupledAxisGenerators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2000
open scoped ContDiff
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularOmegaGraph Grad.AnnularCoupledOrbit Grad.AnnularLowEnergy
open Grad.AnnularKernelOrbit Grad.AnnularInverseCalculus Grad.AnnularOrbitGenerators Grad.AnnularLowOrbit
open Grad.AnnularCoupledInverse Grad.AnnularCrossMaps
attribute [local instance] coupledRealNormed

/-- The literal BF insertion on every stored ORIGINAL coupled graph
coordinate, including all high and four low angular modes. -/
def CoupledInsertedGrade (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (grade : ℕ) (field weighted : CoupledSpace lower length positive lengthPositive) : Prop :=
  (∀ index : HighAnnularMode, weighted.ofLp.1.ofLp.1.val index =
    ((annularFrequency index.val.1 index.val.2 ^ grade : ℝ) : ℂ) • field.ofLp.1.ofLp.1.val index) ∧
  (∀ (coordinate : Fin 2) (index : HighAnnularMode), weighted.ofLp.1.ofLp.2.val coordinate index =
    ((annularFrequency index.val.1 index.val.2 ^ grade : ℝ) : ℂ) • field.ofLp.1.ofLp.2.val coordinate index) ∧
  (∀ (coordinate : Fin 2) (index : LowAnnularIndex), weighted.ofLp.2.val coordinate index =
    ((lowInsertedFrequency index ^ grade : ℝ) : ℂ) • field.ofLp.2.val coordinate index)

theorem hilbertProduct_norm_le_add {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (value : WithLp 2 (E × F)) : ‖value‖ ≤ ‖value.ofLp.1‖ + ‖value.ofLp.2‖ := by
  have squared := WithLp.prod_norm_sq_eq_of_L2 value
  change ‖value‖ ^ 2 = ‖value.ofLp.1‖ ^ 2 + ‖value.ofLp.2‖ ^ 2 at squared
  nlinarith only [squared, norm_nonneg value, norm_nonneg value.ofLp.1, norm_nonneg value.ofLp.2,
    mul_nonneg (norm_nonneg value.ofLp.1) (norm_nonneg value.ofLp.2)]

theorem coupled_norm_le_three (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (value : CoupledSpace lower length positive lengthPositive) :
    ‖value‖ ≤ ‖value.ofLp.1.ofLp.1‖ + ‖value.ofLp.1.ofLp.2‖ + ‖value.ofLp.2‖ :=
  (hilbertProduct_norm_le_add value).trans (add_le_add (hilbertProduct_norm_le_add value.ofLp.1) le_rfl)

def coupledGeneratorGradeConstant (grade : ℕ) : ℝ :=
  3 * (4 : ℝ) ^ grade + 2 * ((3 : ℝ) ^ grade * (2 : ℝ) ^ grade)

theorem coupledGeneratorGradeConstant_nonnegative (grade : ℕ) : 0 ≤ coupledGeneratorGradeConstant grade := by
  unfold coupledGeneratorGradeConstant
  positivity

/-- Genuine angular/cell norm derivatives imply all literal BF graph
coordinates for the SAME field, with no loss depending on the inner radius. -/
theorem coupled_insertedGrade_of_smoothOrbit (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive)
    (smooth : ∀ axis : Bool, ContDiff ℝ ∞ (fun time : ℝ => coupledTranslationEquivalence lower length positive lengthPositive
      (time • axisVector axis) field)) (grade : ℕ) :
    ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted ∧
      ‖weighted‖ ≤ coupledGeneratorGradeConstant grade *
        (‖field‖ + ‖coupledAxisGenerator lower length positive lengthPositive field false grade‖ +
          ‖coupledAxisGenerator lower length positive lengthPositive field true grade‖) := by
  let angular := coupledAxisGenerator lower length positive lengthPositive field false grade
  let cell := coupledAxisGenerator lower length positive lengthPositive field true grade
  have angularEnergy := coupledAxisGenerator_energy lower length positive lengthPositive field false (smooth false) grade
  have cellEnergy := coupledAxisGenerator_energy lower length positive lengthPositive field true (smooth true) grade
  have angularFlux := coupledAxisGenerator_flux lower length positive lengthPositive field false (smooth false) grade
  have cellFlux := coupledAxisGenerator_flux lower length positive lengthPositive field true (smooth true) grade
  have cellLow := coupledAxisGenerator_low lower length positive lengthPositive field true (smooth true) grade
  simp only [axisFrequency, Bool.false_eq_true, if_false, if_true] at angularEnergy cellEnergy angularFlux cellFlux cellLow
  obtain ⟨energyWeighted, energyActual, energyBound⟩ := energy_insertedGrade_of_generators lower length positive
    field.ofLp.1.ofLp.1 angular.ofLp.1.ofLp.1 cell.ofLp.1.ofLp.1 grade angularEnergy cellEnergy
  obtain ⟨fluxWeighted, fluxActual, fluxBound⟩ := flux_insertedGrade_of_generators lower length positive lengthPositive
    field.ofLp.1.ofLp.2 angular.ofLp.1.ofLp.2 cell.ofLp.1.ofLp.2 grade angularFlux cellFlux
  obtain ⟨lowWeighted, lowActual, lowBound⟩ := lowGraph_insertedGrade_of_generator lower length positive
    field.ofLp.2 cell.ofLp.2 grade cellLow
  let weighted : CoupledSpace lower length positive lengthPositive := WithLp.toLp 2
    (WithLp.toLp 2 (energyWeighted, fluxWeighted), lowWeighted)
  refine ⟨weighted, ⟨energyActual, fluxActual, lowActual⟩, ?_⟩
  let total := ‖field‖ + ‖angular‖ + ‖cell‖
  have energyEstimate : ‖energyWeighted‖ ≤ 4 ^ grade * total :=
    energyBound.trans (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add
        (coupledEnergy_bound lower length positive lengthPositive field)
        (coupledEnergy_bound lower length positive lengthPositive angular))
        (coupledEnergy_bound lower length positive lengthPositive cell)) (by positivity))
  have fluxEstimate : ‖fluxWeighted‖ ≤ 2 * 4 ^ grade * total :=
    fluxBound.trans (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add
        (coupledFlux_bound lower length positive lengthPositive field)
        (coupledFlux_bound lower length positive lengthPositive angular))
        (coupledFlux_bound lower length positive lengthPositive cell)) (by positivity))
  have lowEstimate : ‖lowWeighted‖ ≤ 2 * (3 ^ grade * 2 ^ grade) * total := by
    apply lowBound.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have first := coupledLow_bound lower length positive lengthPositive field
    have second := coupledLow_bound lower length positive lengthPositive cell
    change ‖field.ofLp.2‖ ≤ ‖field‖ at first
    change ‖cell.ofLp.2‖ ≤ ‖cell‖ at second
    change ‖field.ofLp.2‖ + ‖cell.ofLp.2‖ ≤ ‖field‖ + ‖angular‖ + ‖cell‖
    exact (add_le_add first second).trans (by linarith only [norm_nonneg angular])
  have combined := (coupled_norm_le_three lower length positive lengthPositive weighted).trans
    (add_le_add (add_le_add energyEstimate fluxEstimate) lowEstimate)
  exact combined.trans_eq (by dsimp [coupledGeneratorGradeConstant, total, angular, cell]; ring)

end Grad.AnnularHighGenerators
