import ASG41InsertedSourceWeights

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryKernelAction Grad.PhaseAlgebra

theorem totalConjugatedCoordinate_storage (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell grade : ℕ)
    (field : AnnularTotalSourceH1 parameters dimension lower angular cell grade) (mode : ℤ × ℤ) (coordinate : Fin 2) :
    weightedRadialCoordinate dimension lower coordinate (field mode) =
      sourceInsertedWeight angular cell grade mode • radialSqrtMap dimension lower
        (totalConjugatedCoordinate parameters dimension lower positive bounded angular cell grade field mode coordinate) := by
  rw [weightedRadialCoordinate_eq_sqrt dimension lower positive bounded]
  unfold totalConjugatedCoordinate totalConjugatedMode
  rw [map_smul, (radialSqrtMap dimension lower).map_smul_of_tower, smul_smul,
    mul_inv_cancel₀ (sourceInsertedWeight_pos angular cell grade mode).ne', one_smul]

theorem totalSourceCoefficient_conjugation (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell grade : ℕ)
    (field : AnnularTotalSourceH1 parameters dimension lower angular cell grade) (mode : ℤ × ℤ) (radius : ℝ) :
    Real.exp (radialPhase parameters radius mode.2) •
      totalSourceCoefficient parameters dimension lower positive bounded angular cell grade field mode radius =
    totalConjugatedCoordinate parameters dimension lower positive bounded angular cell grade field mode 0 radius := by
  rw [totalSourceCoefficient, smul_smul, mul_inv_cancel₀ (Real.exp_pos _).ne', one_smul]

theorem totalSource_literal_norm_sq (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell grade : ℕ)
    (field : AnnularTotalSourceH1 parameters dimension lower angular cell grade) :
    ‖field‖ ^ 2 = ∑' mode : ℤ × ℤ, sourceInsertedWeight angular cell grade mode ^ 2 *
      (∫ radius in lower..1, radius *
        (‖Real.exp (radialPhase parameters radius mode.2) •
          totalSourceCoefficient parameters dimension lower positive bounded angular cell grade field mode radius‖ ^ 2 +
         ‖totalConjugatedCoordinate parameters dimension lower positive bounded angular cell grade field mode 1 radius‖ ^ 2)) := by
  rw [annularSource_norm_sq]
  apply tsum_congr
  intro mode
  rw [totalConjugatedCoordinate_storage parameters dimension lower positive bounded angular cell grade field mode 0,
    totalConjugatedCoordinate_storage parameters dimension lower positive bounded angular cell grade field mode 1]
  simp only [norm_smul, Real.norm_of_nonneg (sourceInsertedWeight_pos angular cell grade mode).le,
    mul_pow, totalSourceCoefficient_conjugation]
  rw [radialSqrtMap_norm_sq dimension lower positive bounded, radialSqrtMap_norm_sq dimension lower positive bounded]
  rw [← mul_add, ← intervalIntegral.integral_add
    (radialWeightedEnergy_integrable dimension lower positive bounded
      (totalConjugatedCoordinate parameters dimension lower positive bounded angular cell grade field mode 0))
    (radialWeightedEnergy_integrable dimension lower positive bounded
      (totalConjugatedCoordinate parameters dimension lower positive bounded angular cell grade field mode 1))]
  congr 1
  apply intervalIntegral.integral_congr
  intro radius _
  ring

theorem sourceInsertedWeight_sq (angular cell grade : ℕ) (mode : ℤ × ℤ) :
    sourceInsertedWeight angular cell grade mode ^ 2 =
      annularFrequency mode.1 mode.2 ^ (2 * grade) *
      (1 + |(mode.1 : ℝ)|) ^ (2 * angular) * (1 + |(mode.2 : ℝ)|) ^ (2 * cell) := by
  unfold sourceInsertedWeight splitTangentialWeight
  simp only [mul_pow, ← pow_mul]
  rw [Nat.mul_comm grade 2, Nat.mul_comm angular 2, Nat.mul_comm cell 2]
  ring

theorem totalSourceCoefficient_faithful (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell grade : ℕ)
    (first second : AnnularTotalSourceH1 parameters dimension lower angular cell grade)
    (same : ∀ mode : ℤ × ℤ, ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      totalSourceCoefficient parameters dimension lower positive bounded angular cell grade first mode radius =
      totalSourceCoefficient parameters dimension lower positive bounded angular cell grade second mode radius) : first = second := by
  apply annularSource_bulk_injective parameters dimension lower positive bounded angular cell
  apply Subtype.ext
  funext mode
  rw [annularSourceCoordinate_apply, annularSourceCoordinate_apply,
    totalConjugatedCoordinate_storage parameters dimension lower positive bounded angular cell grade first mode 0,
    totalConjugatedCoordinate_storage parameters dimension lower positive bounded angular cell grade second mode 0]
  congr 2
  apply Lp.ext
  filter_upwards [same mode] with radius sameValue
  rw [← totalSourceCoefficient_conjugation parameters dimension lower positive bounded angular cell grade first mode radius,
    ← totalSourceCoefficient_conjugation parameters dimension lower positive bounded angular cell grade second mode radius,
    sameValue]

end Grad.AnnularSourceGraph
