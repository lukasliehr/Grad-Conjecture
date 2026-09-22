import AJV6OriginalNormalizedLowRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.CartesianState Grad.AnnularSourceGraph Grad.AnnularLowEnergy
open Grad.AnnularOriginalLow Grad.CircularHighRegularity Grad.AnnularVariational Grad.AnnularReconstruction
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem collarWeakDerivative_unique (dimension : ℕ) (lower : ℝ)
    (field first second : CollarL2 (ComplexEuclidean dimension) lower)
    (firstWeak : CollarWeakDerivative lower field first) (secondWeak : CollarWeakDerivative lower field second) :
    first = second := by
  apply sub_eq_zero.mp
  apply collarPairing_separates lower
  intro test vector
  rw [map_sub, firstWeak test vector, secondWeak test vector, sub_self]

theorem collarWeakDerivative_real_smul (dimension : ℕ) (lower scalar : ℝ)
    (field derivative : CollarL2 (ComplexEuclidean dimension) lower)
    (weak : CollarWeakDerivative lower field derivative) :
    CollarWeakDerivative lower (scalar • field) (scalar • derivative) := by
  intro test vector
  rw [map_smul, map_smul, weak test vector, smul_neg]

/-- The second original AJ coordinate is Lambda^-1 v', and it has exactly
the SAME constant endpoint ratio as v. No derivative coordinate is dropped. -/
theorem originalLowEndpointRestriction_slope (parameters : PhaseParameters) (lower upper length : ℝ)
    (included : lower ≤ upper) (positiveLower : 0 < lower) (positiveUpper : 0 < upper)
    (bounded : upper < 1) (lengthPositive : 0 < length) (field : originalLowGraph lower)
    (index : LowAnnularIndex) :
    (originalLowEndpointRestriction parameters lower upper length included positiveLower positiveUpper bounded lengthPositive field).val 1 index =
      originalLowEndpointRatio parameters lower upper length index •
        collarL2Restriction 1 lower upper included (field.val 1 index) := by
  let output := originalLowEndpointRestriction parameters lower upper length included positiveLower positiveUpper bounded lengthPositive field
  let scalar : ℝ := originalLowEndpointRatio parameters lower upper length index
  have valueSame : output.val 0 index = scalar • collarL2Restriction 1 lower upper included (field.val 0 index) :=
    originalLowEndpointRestriction_value parameters lower upper length included positiveLower positiveUpper bounded lengthPositive field index
  have source := collarWeakDerivative_restrict 1 lower upper included positiveUpper bounded _ _ (field.property index)
  change CollarWeakDerivative upper (collarL2Restriction 1 lower upper included (field.val 0 index))
    (collarL2Restriction 1 lower upper included ((cellFrequency index.2.val.2 : ℂ) • field.val 1 index)) at source
  rw [map_smul] at source
  have scaled := collarWeakDerivative_real_smul 1 upper scalar _ _ source
  rw [← valueSame] at scaled
  have target := output.property index
  change CollarWeakDerivative upper (output.val 0 index)
    ((cellFrequency index.2.val.2 : ℂ) • output.val 1 index) at target
  have same := collarWeakDerivative_unique 1 upper _ _ _ target scaled
  have nonzero : (cellFrequency index.2.val.2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (cellFrequency_pos index.2.val.2).ne'
  have result : output.val 1 index = scalar • collarL2Restriction 1 lower upper included (field.val 1 index) := by
    apply smul_right_injective (CollarL2 (ComplexEuclidean 1) upper) nonzero
    exact same.trans (smul_comm scalar (cellFrequency index.2.val.2 : ℂ) _)
  exact result

theorem lowEnergyRestriction_id (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) :
    lowEnergyRestriction lower lower length le_rfl positive positive bounded field = field := by
  apply Subtype.ext
  apply PiLp.ext
  intro slot
  apply lp.ext
  funext index
  exact collarL2Restriction_id 1 lower (field.val slot index)

theorem lowEnergyRestriction_comp (lower middle upper length : ℝ)
    (first : lower ≤ middle) (second : middle ≤ upper)
    (positiveLower : 0 < lower) (positiveMiddle : 0 < middle) (positiveUpper : 0 < upper)
    (bounded : upper < 1) (field : lowEnergyGraph lower length positiveLower) :
    lowEnergyRestriction middle upper length second positiveMiddle positiveUpper bounded
      (lowEnergyRestriction lower middle length first positiveLower positiveMiddle (second.trans_lt bounded) field) =
    lowEnergyRestriction lower upper length (first.trans second) positiveLower positiveUpper bounded field := by
  apply Subtype.ext
  apply PiLp.ext
  intro slot
  apply lp.ext
  funext index
  exact collarL2Restriction_comp 1 lower middle upper first second (field.val slot index)

theorem originalLowEndpointRestriction_id (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length) (field : originalLowGraph lower) :
    originalLowEndpointRestriction parameters lower lower length le_rfl positive positive bounded lengthPositive field = field := by
  apply (originalLowGraphEquivalence parameters lower length positive lengthPositive bounded.le).injective
  rw [originalLowEndpointRestriction_weighted, lowEnergyRestriction_id]

theorem originalLowEndpointRestriction_comp (parameters : PhaseParameters) (lower middle upper length : ℝ)
    (first : lower ≤ middle) (second : middle ≤ upper)
    (positiveLower : 0 < lower) (positiveMiddle : 0 < middle) (positiveUpper : 0 < upper)
    (bounded : upper < 1) (lengthPositive : 0 < length) (field : originalLowGraph lower) :
    originalLowEndpointRestriction parameters middle upper length second positiveMiddle positiveUpper bounded lengthPositive
      (originalLowEndpointRestriction parameters lower middle length first positiveLower positiveMiddle
        (second.trans_lt bounded) lengthPositive field) =
    originalLowEndpointRestriction parameters lower upper length (first.trans second) positiveLower positiveUpper bounded lengthPositive field := by
  apply (originalLowGraphEquivalence parameters upper length positiveUpper lengthPositive bounded.le).injective
  rw [originalLowEndpointRestriction_weighted, originalLowEndpointRestriction_weighted,
    originalLowEndpointRestriction_weighted, lowEnergyRestriction_comp]

/-- Every bounded original angular/cell/inserted-grade diagonal commutes
with this endpoint-changing map, on both complete derivative coordinates. -/
theorem originalLowEndpointRestriction_diagonal (parameters : PhaseParameters) (lower upper length : ℝ)
    (included : lower ≤ upper) (positiveLower : 0 < lower) (positiveUpper : 0 < upper)
    (bounded : upper < 1) (lengthPositive : 0 < length)
    (coefficient : LowAnnularIndex → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (coefficientBound : ∀ index, |coefficient index| ≤ constant) (field : originalLowGraph lower) :
    originalLowEndpointRestriction parameters lower upper length included positiveLower positiveUpper bounded lengthPositive
      (originalLowGraphDiagonal lower coefficient constant nonnegative coefficientBound field) =
    originalLowGraphDiagonal upper coefficient constant nonnegative coefficientBound
      (originalLowEndpointRestriction parameters lower upper length included positiveLower positiveUpper bounded lengthPositive field) := by
  apply originalLowGraph_value_injective upper
  apply lp.ext
  funext index
  change (originalLowEndpointRestriction parameters lower upper length included positiveLower positiveUpper bounded lengthPositive
      (originalLowGraphDiagonal lower coefficient constant nonnegative coefficientBound field)).val 0 index =
    (coefficient index : ℂ) •
      (originalLowEndpointRestriction parameters lower upper length included positiveLower positiveUpper bounded lengthPositive field).val 0 index
  rw [originalLowEndpointRestriction_value, originalLowEndpointRestriction_value]
  change originalLowEndpointRatio parameters lower upper length index •
      collarL2Restriction 1 lower upper included ((coefficient index : ℂ) • field.val 0 index) = _
  rw [map_smul, smul_comm]

end Grad.AnnularRestriction
