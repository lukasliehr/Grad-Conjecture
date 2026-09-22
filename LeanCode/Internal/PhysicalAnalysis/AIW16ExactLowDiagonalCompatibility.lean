import AIW15OriginalLowGraphEquivalence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularOriginalLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.PhaseAlgebra Grad.CircularHighRegularity
open Grad.AnnularGrades Grad.AnnularReconstruction Grad.GaugeCoefficients.Physical.WeightedTrace

variable (lower : ℝ) (coefficient : LowAnnularIndex → ℝ) (constant : ℝ)
  (nonnegative : 0 ≤ constant) (coefficientBound : ∀ index, |coefficient index| ≤ constant)

def originalLowDiagonal : LowEnergyAmbient lower →L[ℂ] LowEnergyAmbient lower :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => LowEnergyBulk lower)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun coordinate =>
      (realLpDiagonal coefficient constant nonnegative coefficientBound).comp (PiLp.proj 2 _ coordinate)))

theorem originalLowDiagonal_apply (field : LowEnergyAmbient lower) (coordinate : Fin 2) (index : LowAnnularIndex) :
    originalLowDiagonal lower coefficient constant nonnegative coefficientBound field coordinate index =
      (coefficient index : ℂ) • field coordinate index := rfl

def originalLowGraphDiagonal : originalLowGraph lower →L[ℂ] originalLowGraph lower :=
  ((originalLowDiagonal lower coefficient constant nonnegative coefficientBound).comp (originalLowGraph lower).subtypeL).codRestrict
    (originalLowGraph lower) (fun field => by
      intro index
      change CollarWeakDerivative lower ((coefficient index : ℂ) • field.val 0 index)
        ((cellFrequency index.2.val.2 : ℂ) • ((coefficient index : ℂ) • field.val 1 index))
      rw [smul_comm (cellFrequency index.2.val.2 : ℂ) (coefficient index : ℂ)]
      exact collarWeakDerivative_complex_smul lower (coefficient index : ℂ) _ _ (field.property index))

def originalLowEnergyDiagonal (length : ℝ) (positive : 0 < lower) :
    lowEnergyGraph lower length positive →L[ℂ] lowEnergyGraph lower length positive :=
  ((originalLowDiagonal lower coefficient constant nonnegative coefficientBound).comp
    (lowEnergyGraph lower length positive).subtypeL).codRestrict (lowEnergyGraph lower length positive) (fun field => by
      intro index
      change CollarWeakDerivative lower
        (collarScalar 1 lower (lowStorageInverse lower positive) ((coefficient index : ℂ) • field.val 0 index))
        (collarScalar 1 lower (lowMuCurve lower length positive index.2.val.2)
          (collarScalar 1 lower (lowStorageInverse lower positive) ((coefficient index : ℂ) • field.val 1 index)))
      simp only [map_smul]
      exact collarWeakDerivative_complex_smul lower (coefficient index : ℂ) _ _ (field.property index))

theorem originalLowWeight_diagonal (parameters : PhaseParameters) (length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1) (field : originalLowGraph lower) :
    originalLowWeight parameters lower length positive lengthPositive bounded
      (originalLowGraphDiagonal lower coefficient constant nonnegative coefficientBound field) =
    originalLowEnergyDiagonal lower coefficient constant nonnegative coefficientBound length positive
      (originalLowWeight parameters lower length positive lengthPositive bounded field) := by
  apply lowEnergyGraph_value_injective lower length positive
  apply lp.ext
  funext index
  change collarScalar 1 lower (originalLowFromAJValueCurve parameters lower length positive lengthPositive index)
      ((coefficient index : ℂ) • field.val 0 index) =
    (coefficient index : ℂ) • collarScalar 1 lower (originalLowFromAJValueCurve parameters lower length positive lengthPositive index)
      (field.val 0 index)
  exact map_smul _ _ _

theorem originalLowUnweight_diagonal (parameters : PhaseParameters) (length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1)
    (field : lowEnergyGraph lower length positive) :
    originalLowUnweight parameters lower length positive lengthPositive bounded
      (originalLowEnergyDiagonal lower coefficient constant nonnegative coefficientBound length positive field) =
    originalLowGraphDiagonal lower coefficient constant nonnegative coefficientBound
      (originalLowUnweight parameters lower length positive lengthPositive bounded field) := by
  apply originalLowGraph_value_injective lower
  apply lp.ext
  funext index
  change collarScalar 1 lower (originalLowToAJValueCurve parameters lower length positive index)
      ((coefficient index : ℂ) • field.val 0 index) =
    (coefficient index : ℂ) • collarScalar 1 lower (originalLowToAJValueCurve parameters lower length positive index)
      (field.val 0 index)
  exact map_smul _ _ _

theorem originalLowDiagonal_bound (field : LowEnergyAmbient lower) :
    ‖originalLowDiagonal lower coefficient constant nonnegative coefficientBound field‖ ≤ constant * ‖field‖ := by
  let output := originalLowDiagonal lower coefficient constant nonnegative coefficientBound field
  have first := realLpDiagonal_bound coefficient constant nonnegative coefficientBound (field 0)
  have second := realLpDiagonal_bound coefficient constant nonnegative coefficientBound (field 1)
  have firstSquare := mul_self_le_mul_self (norm_nonneg _) first
  have secondSquare := mul_self_le_mul_self (norm_nonneg _) second
  have input : ‖field‖ ^ 2 = ‖field 0‖ ^ 2 + ‖field 1‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  have outputNorm : ‖output‖ ^ 2 = ‖output 0‖ ^ 2 + ‖output 1‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  change ‖output 0‖ * ‖output 0‖ ≤ (constant * ‖field 0‖) * (constant * ‖field 0‖) at firstSquare
  change ‖output 1‖ * ‖output 1‖ ≤ (constant * ‖field 1‖) * (constant * ‖field 1‖) at secondSquare
  change ‖output‖ ≤ _
  nlinarith [norm_nonneg output, mul_nonneg nonnegative (norm_nonneg field),
    mul_nonneg (sq_nonneg constant) (sq_nonneg ‖field‖)]

end Grad.AnnularOriginalLow
