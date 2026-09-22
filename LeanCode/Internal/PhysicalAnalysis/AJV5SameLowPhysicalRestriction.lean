import AJV4LowStoredGraphRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.CartesianState Grad.AnnularSourceGraph Grad.AnnularLowEnergy
open Grad.AnnularFluxTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

def radialSectionRestriction (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper)
    (sectionValue : RadialContinuousSection dimension lower) : RadialContinuousSection dimension upper where
  toFun radius := sectionValue ⟨radius.val, included.trans radius.property.1, radius.property.2⟩
  continuous_toFun := sectionValue.continuous.comp
    (continuous_subtype_val.subtype_mk (fun radius => ⟨included.trans radius.property.1, radius.property.2⟩))

theorem radialSectionL2_restrict (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper)
    (positiveLower : 0 < lower) (positiveUpper : 0 < upper) (bounded : upper ≤ 1)
    (sectionValue : RadialContinuousSection dimension lower) :
    radialSectionL2 dimension upper positiveUpper bounded (radialSectionRestriction dimension lower upper included sectionValue) =
      collarL2Restriction dimension lower upper included
        (radialSectionL2 dimension lower positiveLower (included.trans bounded) sectionValue) := by
  apply Lp.ext
  have original := (collarContinuous_memLp (ComplexEuclidean dimension) lower
    (radialSectionExtension dimension lower (included.trans bounded) sectionValue)).coeFn_toLp
  have restricted := (collarContinuous_memLp (ComplexEuclidean dimension) upper
    (radialSectionExtension dimension upper bounded (radialSectionRestriction dimension lower upper included sectionValue))).coeFn_toLp
  filter_upwards [collarL2Restriction_ae dimension lower upper included
      (radialSectionL2 dimension lower positiveLower (included.trans bounded) sectionValue),
    original.filter_mono (ae_mono (collarMeasure_le lower upper included)), restricted,
    ae_restrict_mem measurableSet_Icc] with radius actual source target inside
  change radialSectionL2 dimension lower positiveLower (included.trans bounded) sectionValue radius = _ at source
  change radialSectionL2 dimension upper positiveUpper bounded
    (radialSectionRestriction dimension lower upper included sectionValue) radius = _ at target
  rw [actual, source, target]
  change sectionValue ⟨(radialClamp upper bounded radius).val,
      included.trans (radialClamp upper bounded radius).property.1,
      (radialClamp upper bounded radius).property.2⟩ =
    sectionValue (radialClamp lower (included.trans bounded) radius)
  rw [radialClamp_eq upper bounded radius inside,
    radialClamp_eq lower (included.trans bounded) radius (Icc_subset_Icc included le_rfl inside)]

theorem lowEnergyRestriction_section (lower upper length : ℝ) (included : lower ≤ upper)
    (positiveLower : 0 < lower) (positiveUpper : 0 < upper) (bounded : upper < 1)
    (field : lowEnergyGraph lower length positiveLower) (index : LowAnnularIndex) :
    lowEnergySection upper length positiveUpper bounded
      (lowEnergyRestriction lower upper length included positiveLower positiveUpper bounded field) index =
    radialSectionRestriction 1 lower upper included
      (lowEnergySection lower length positiveLower (included.trans_lt bounded) field index) := by
  apply radialSectionL2_injective upper positiveUpper bounded
  rw [lowEnergySection_bulk, radialSectionL2_restrict, lowEnergySection_bulk]
  exact lowAmbientRestriction_value lower upper included positiveLower positiveUpper field.val index

/-- The actual xi and x are unchanged by the new endpoint normalization. -/
theorem lowEnergyRestriction_physical (parameters : PhaseParameters) (lower upper length : ℝ)
    (included : lower ≤ upper) (positiveLower : 0 < lower) (positiveUpper : 0 < upper) (bounded : upper < 1)
    (field : lowEnergyGraph lower length positiveLower) (index : LowAnnularIndex)
    (radius : Icc upper (1 : ℝ)) :
    lowPhysicalSection parameters upper length positiveUpper bounded
      (lowEnergyRestriction lower upper length included positiveLower positiveUpper bounded field) index radius =
    lowPhysicalSection parameters lower length positiveLower (included.trans_lt bounded) field index
      ⟨radius.val, included.trans radius.property.1, radius.property.2⟩ := by
  have same := congrArg (fun sectionValue : RadialContinuousSection 1 upper => sectionValue radius)
    (lowEnergyRestriction_section lower upper length included positiveLower positiveUpper bounded field index)
  change lowEnergySection upper length positiveUpper bounded
      (lowEnergyRestriction lower upper length included positiveLower positiveUpper bounded field) index radius =
    lowEnergySection lower length positiveLower (included.trans_lt bounded) field index
      ⟨radius.val, included.trans radius.property.1, radius.property.2⟩ at same
  have first := lowPhysicalSection_encode parameters upper length positiveUpper bounded
    (lowEnergyRestriction lower upper length included positiveLower positiveUpper bounded field) index radius
  have second := lowPhysicalSection_encode parameters lower length positiveLower (included.trans_lt bounded)
    field index ⟨radius.val, included.trans radius.property.1, radius.property.2⟩
  exact smul_right_injective (ComplexEuclidean 1)
    (lowPhysicalFactor_pos parameters length radius.val (positiveUpper.trans_le radius.property.1) index).ne'
    (first.trans (same.trans second.symm))

/-- Incoming values at the new endpoint are the SAME physical section
evaluated there; no zero condition at the old endpoint is transported. -/
theorem lowEnergyRestriction_newIncoming (parameters : PhaseParameters) (lower upper length : ℝ)
    (included : lower ≤ upper) (positiveLower : 0 < lower) (positiveUpper : 0 < upper) (bounded : upper < 1)
    (field : lowEnergyGraph lower length positiveLower) (index : LowAnnularIndex) :
    lowPhysicalSection parameters upper length positiveUpper bounded
      (lowEnergyRestriction lower upper length included positiveLower positiveUpper bounded field) index
      ⟨upper, le_rfl, bounded.le⟩ =
    lowPhysicalSection parameters lower length positiveLower (included.trans_lt bounded) field index
      ⟨upper, included, bounded.le⟩ :=
  lowEnergyRestriction_physical parameters lower upper length included positiveLower positiveUpper bounded field index _

theorem lowEnergyRestriction_outer (parameters : PhaseParameters) (lower upper length : ℝ)
    (included : lower ≤ upper) (positiveLower : 0 < lower) (positiveUpper : 0 < upper) (bounded : upper < 1)
    (field : lowEnergyGraph lower length positiveLower) (index : LowAnnularIndex) :
    lowPhysicalSection parameters upper length positiveUpper bounded
      (lowEnergyRestriction lower upper length included positiveLower positiveUpper bounded field) index
      ⟨1, bounded.le, le_rfl⟩ =
    lowPhysicalSection parameters lower length positiveLower (included.trans_lt bounded) field index
      ⟨1, included.trans bounded.le, le_rfl⟩ :=
  lowEnergyRestriction_physical parameters lower upper length included positiveLower positiveUpper bounded field index _

end Grad.AnnularRestriction
