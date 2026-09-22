import AJV5SameLowPhysicalRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.CartesianState Grad.AnnularSourceGraph Grad.AnnularLowEnergy
open Grad.AnnularOriginalLow Grad.CircularHighRegularity Grad.AnnularVariational
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Literal AJ endpoint change S_d S_c^-1 on (Lambda xi,x). -/
def originalLowEndpointRatio (parameters : PhaseParameters) (lower upper length : ℝ)
    (index : LowAnnularIndex) : ℝ :=
  if index.1 = 0 then originalLowScale parameters upper length index.2 /
    originalLowScale parameters lower length index.2 else 1

theorem originalLowEndpoint_factor (parameters : PhaseParameters) (lower upper length : ℝ)
    (positiveLower : 0 < lower) (lengthPositive : 0 < length)
    (index : LowAnnularIndex) (radius : ℝ) :
    originalLowAJPhysicalFactor parameters upper length radius index =
      originalLowEndpointRatio parameters lower upper length index *
        originalLowAJPhysicalFactor parameters lower length radius index := by
  have nonzero := (originalLowScale_positive parameters lower length positiveLower lengthPositive index.2).ne'
  by_cases entry : index.1 = 0
  · simp only [originalLowAJPhysicalFactor, originalLowEndpointRatio, if_pos entry]
    field_simp
  · simp only [originalLowAJPhysicalFactor, originalLowEndpointRatio, if_neg entry, one_mul]

theorem originalLowEndpoint_section (parameters : PhaseParameters) (lower upper length : ℝ)
    (included : lower ≤ upper) (positiveLower : 0 < lower) (positiveUpper : 0 < upper)
    (bounded : upper < 1) (lengthPositive : 0 < length)
    (field : lowEnergyGraph lower length positiveLower) (index : LowAnnularIndex) :
    originalLowAJSection parameters upper length positiveUpper bounded
      (lowEnergyRestriction lower upper length included positiveLower positiveUpper bounded field) index =
      originalLowEndpointRatio parameters lower upper length index •
        radialSectionRestriction 1 lower upper included
          (originalLowAJSection parameters lower length positiveLower (included.trans_lt bounded) field index) := by
  apply ContinuousMap.ext
  intro radius
  change originalLowAJSection parameters upper length positiveUpper bounded
      (lowEnergyRestriction lower upper length included positiveLower positiveUpper bounded field) index radius =
    originalLowEndpointRatio parameters lower upper length index •
      originalLowAJSection parameters lower length positiveLower (included.trans_lt bounded) field index
        ⟨radius.val, included.trans radius.property.1, radius.property.2⟩
  rw [originalLowAJSection_physical, originalLowAJSection_physical,
    lowEnergyRestriction_physical, originalLowEndpoint_factor parameters lower upper length positiveLower lengthPositive,
    mul_smul]

/-- V1's actual low retained restriction, through the accepted two-way BF6
maps and the contraction on the literal weighted weak graph. -/
def originalLowEndpointRestriction (parameters : PhaseParameters) (lower upper length : ℝ)
    (included : lower ≤ upper) (positiveLower : 0 < lower) (positiveUpper : 0 < upper)
    (bounded : upper < 1) (lengthPositive : 0 < length) :
    originalLowGraph lower →L[ℂ] originalLowGraph upper :=
  (originalLowGraphEquivalence parameters upper length positiveUpper lengthPositive bounded.le).symm.toContinuousLinearMap.comp
    ((lowEnergyRestriction lower upper length included positiveLower positiveUpper bounded).comp
      (originalLowGraphEquivalence parameters lower length positiveLower lengthPositive (included.trans bounded.le)).toContinuousLinearMap)

theorem originalLowEndpointRestriction_weighted (parameters : PhaseParameters) (lower upper length : ℝ)
    (included : lower ≤ upper) (positiveLower : 0 < lower) (positiveUpper : 0 < upper)
    (bounded : upper < 1) (lengthPositive : 0 < length) (field : originalLowGraph lower) :
    originalLowGraphEquivalence parameters upper length positiveUpper lengthPositive bounded.le
      (originalLowEndpointRestriction parameters lower upper length included positiveLower positiveUpper bounded lengthPositive field) =
    lowEnergyRestriction lower upper length included positiveLower positiveUpper bounded
      (originalLowGraphEquivalence parameters lower length positiveLower lengthPositive (included.trans bounded.le) field) :=
  (originalLowGraphEquivalence parameters upper length positiveUpper lengthPositive bounded.le).apply_symm_apply _

theorem originalLowEndpointRestriction_value (parameters : PhaseParameters) (lower upper length : ℝ)
    (included : lower ≤ upper) (positiveLower : 0 < lower) (positiveUpper : 0 < upper)
    (bounded : upper < 1) (lengthPositive : 0 < length) (field : originalLowGraph lower)
    (index : LowAnnularIndex) :
    (originalLowEndpointRestriction parameters lower upper length included positiveLower positiveUpper bounded lengthPositive field).val 0 index =
      originalLowEndpointRatio parameters lower upper length index •
        collarL2Restriction 1 lower upper included (field.val 0 index) := by
  let weighted := originalLowGraphEquivalence parameters lower length positiveLower lengthPositive (included.trans bounded.le) field
  let restricted := lowEnergyRestriction lower upper length included positiveLower positiveUpper bounded weighted
  have source := originalLowBF6_section_bulk parameters lower length positiveLower lengthPositive
    (included.trans_lt bounded) weighted index
  have sourceSame :
      (originalLowGraphEquivalence parameters lower length positiveLower lengthPositive (included.trans bounded.le)).symm weighted = field :=
    (originalLowGraphEquivalence parameters lower length positiveLower lengthPositive (included.trans bounded.le)).symm_apply_apply field
  rw [sourceSame] at source
  have target := originalLowBF6_section_bulk parameters upper length positiveUpper lengthPositive bounded restricted index
  change ((originalLowGraphEquivalence parameters upper length positiveUpper lengthPositive bounded.le).symm restricted).val 0 index = _
  rw [← target, originalLowEndpoint_section parameters lower upper length included positiveLower positiveUpper bounded lengthPositive weighted,
    map_smul, radialSectionL2_restrict 1 lower upper included positiveLower positiveUpper bounded.le, source]

/-- A bound between these two fixed collars. Its retained-coordinate factor
is the actual BF6 operator norm product, with no uniform moving trace claim. -/
theorem originalLowEndpointRestriction_bound (parameters : PhaseParameters) (lower upper length : ℝ)
    (included : lower ≤ upper) (positiveLower : 0 < lower) (positiveUpper : 0 < upper)
    (bounded : upper < 1) (lengthPositive : 0 < length) (field : originalLowGraph lower) :
    ‖originalLowEndpointRestriction parameters lower upper length included positiveLower positiveUpper bounded lengthPositive field‖ ≤
      ‖(originalLowGraphEquivalence parameters upper length positiveUpper lengthPositive bounded.le).symm.toContinuousLinearMap‖ *
      ‖(originalLowGraphEquivalence parameters lower length positiveLower lengthPositive (included.trans bounded.le)).toContinuousLinearMap‖ * ‖field‖ := by
  let forward := (originalLowGraphEquivalence parameters lower length positiveLower lengthPositive (included.trans bounded.le)).toContinuousLinearMap
  let backward := (originalLowGraphEquivalence parameters upper length positiveUpper lengthPositive bounded.le).symm.toContinuousLinearMap
  have restricted := lowEnergyRestriction_bound lower upper length included positiveLower positiveUpper bounded (forward field)
  have inverse := backward.le_opNorm (lowEnergyRestriction lower upper length included positiveLower positiveUpper bounded (forward field))
  have first := forward.le_opNorm field
  change ‖backward (lowEnergyRestriction lower upper length included positiveLower positiveUpper bounded (forward field))‖ ≤
    ‖backward‖ * ‖forward‖ * ‖field‖
  exact inverse.trans ((mul_le_mul_of_nonneg_left (restricted.trans first) (norm_nonneg backward)).trans_eq (mul_assoc _ _ _).symm)

end Grad.AnnularRestriction
