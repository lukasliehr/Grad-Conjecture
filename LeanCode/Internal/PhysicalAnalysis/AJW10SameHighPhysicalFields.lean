import AJW9HighOuterTraceRestriction
import AJV5SameLowPhysicalRestriction
import AJI22ActualHighSectionStorage

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 250000
open Set Filter MeasureTheory
open scoped Topology
namespace Grad.AnnularRestriction
open Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.AnnularOmegaGraph
open Grad.AnnularHighTilt Grad.AnnularTiltedReference Grad.AnnularSmoothCore Grad.AnnularCrossMaps
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem highEnergySection_bulk (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : annularEnergySpace lower length positive) (mode : HighAnnularMode) :
    radialSectionL2 1 lower positive bounded.le
      (weightedRadialSection 1 lower positive bounded (annularModeRadialH1 lower length positive mode field)) =
    radialOrdinary 1 lower positive (annularEnergyValue lower length positive field mode) :=
  (weightedRadialSection_bulk 1 lower positive bounded (annularModeRadialH1 lower length positive mode field)).trans
    (annularEnergyValue_ordinary lower length positive bounded.le mode field).symm

variable (lower upper length : ℝ) (lowerPositive : 0 < lower) (upperPositive : 0 < upper)
    (upperBounded : upper < 1) (lengthPositive : 0 < length) (included : lower ≤ upper)

theorem highEnergyRestriction_section (field : annularEnergySpace lower length lowerPositive) (mode : HighAnnularMode) :
    weightedRadialSection 1 upper upperPositive upperBounded
      (annularModeRadialH1 upper length upperPositive mode
        (highEnergyRestriction lower upper length lowerPositive upperPositive included field)) =
    radialSectionRestriction 1 lower upper included
      (weightedRadialSection 1 lower lowerPositive (included.trans_lt upperBounded)
        (annularModeRadialH1 lower length lowerPositive mode field)) := by
  apply radialSectionL2_injective upper upperPositive upperBounded
  rw [highEnergySection_bulk, radialSectionL2_restrict 1 lower upper included lowerPositive upperPositive upperBounded.le, highEnergySection_bulk]
  exact (congrArg (radialOrdinary 1 upper upperPositive)
    (congrArg (fun value : AnnularBulk upper => value mode)
      (highEnergyRestriction_value lower upper length lowerPositive upperPositive included field))).trans
    (collarL2Restriction_radialOrdinary lower upper lowerPositive upperPositive included
      (annularEnergyValue lower length lowerPositive field mode)).symm

theorem highOmegaRestriction_section (field : annularOmegaGraph lower length lowerPositive lengthPositive) (mode : HighAnnularMode) :
    annularFluxSection upper upperPositive upperBounded
      (annularOmegaIntoNu upper length upperPositive lengthPositive
        (highOmegaRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field)) mode =
    radialSectionRestriction 1 lower upper included
      (annularFluxSection lower lowerPositive (included.trans_lt upperBounded)
        (annularOmegaIntoNu lower length lowerPositive lengthPositive field) mode) := by
  apply radialSectionL2_injective upper upperPositive upperBounded
  rw [annularFluxSection_bulk, radialSectionL2_restrict, annularFluxSection_bulk]
  change radialOrdinary 1 upper upperPositive (collarL2Restriction 1 lower upper included (field.val 0 mode)) =
    collarL2Restriction 1 lower upper included (radialOrdinary 1 lower lowerPositive (field.val 0 mode))
  exact (collarL2Restriction_radialOrdinary lower upper lowerPositive upperPositive included (field.val 0 mode)).symm

include upperBounded in
theorem highEnergyRestriction_bDecode (field : annularEnergySpace lower length lowerPositive) :
    highEnergyRestriction lower upper length lowerPositive upperPositive included
      (bEnergyDecode lower length lowerPositive field) =
    bEnergyDecode upper length upperPositive
      (highEnergyRestriction lower upper length lowerPositive upperPositive included field) :=
  highEnergyRestriction_diagonal lower upper length lowerPositive upperPositive upperBounded included _ _ _ _ field

/-- The actual physical xi, including the original b decoder, inverse phase,
and r^(9/4) undoing of the weighted high variable. -/
def weightedHighXiPhysicalSection (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (field : annularEnergySpace lower length positive)
    (mode : HighAnnularMode) : RadialContinuousSection 1 lower :=
  radialSectionScalar lower (highPowerCurve lower highTiltExponent positive)
    (annularPhysicalValueSection parameters lower length positive bounded mode
      (bEnergyDecode lower length positive field))

def weightedHighXPhysicalSection (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : annularOmegaGraph lower length positive lengthPositive) (mode : HighAnnularMode) : RadialContinuousSection 1 lower :=
  radialSectionScalar lower (highPowerCurve lower highTiltExponent positive)
    (actualFluxPhysicalSection lower positive bounded parameters
      (annularOmegaIntoNu lower length positive lengthPositive field) mode)

/-- SAME physical xi on every point of the smaller closed collar. -/
theorem highEnergyRestriction_physical (parameters : PhaseParameters)
    (field : annularEnergySpace lower length lowerPositive) (mode : HighAnnularMode) (radius : Icc upper (1 : ℝ)) :
    weightedHighXiPhysicalSection parameters upper length upperPositive upperBounded
      (highEnergyRestriction lower upper length lowerPositive upperPositive included field) mode radius =
    weightedHighXiPhysicalSection parameters lower length lowerPositive (included.trans_lt upperBounded) field mode
      ⟨radius.val, included.trans radius.property.1, radius.property.2⟩ := by
  have same := congrArg (fun sectionValue : RadialContinuousSection 1 upper => sectionValue radius)
    (highEnergyRestriction_section lower upper length lowerPositive upperPositive upperBounded included
      (bEnergyDecode lower length lowerPositive field) mode)
  rw [highEnergyRestriction_bDecode lower upper length lowerPositive upperPositive upperBounded included] at same
  change highPowerCurve upper highTiltExponent upperPositive radius.val •
    (annularInversePhase parameters mode.val.2 radius.val • (_ : ComplexEuclidean 1)) =
    highPowerCurve lower highTiltExponent lowerPositive radius.val •
      (annularInversePhase parameters mode.val.2 radius.val • (_ : ComplexEuclidean 1))
  exact congrArg₂ (fun (factor : ℝ) (value : ComplexEuclidean 1) => factor •
    (annularInversePhase parameters mode.val.2 radius.val • value))
    ((highPowerCurve_physical upper highTiltExponent upperPositive radius.val radius.property).trans
      (highPowerCurve_physical lower highTiltExponent lowerPositive radius.val
        ⟨included.trans radius.property.1, radius.property.2⟩).symm) same

/-- SAME physical x on every point, with the actual omega-to-nu weak graph. -/
theorem highOmegaRestriction_physical (parameters : PhaseParameters)
    (field : annularOmegaGraph lower length lowerPositive lengthPositive) (mode : HighAnnularMode) (radius : Icc upper (1 : ℝ)) :
    weightedHighXPhysicalSection parameters upper length upperPositive upperBounded lengthPositive
      (highOmegaRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field) mode radius =
    weightedHighXPhysicalSection parameters lower length lowerPositive (included.trans_lt upperBounded) lengthPositive field mode
      ⟨radius.val, included.trans radius.property.1, radius.property.2⟩ := by
  have same := congrArg (fun sectionValue : RadialContinuousSection 1 upper => sectionValue radius)
    (highOmegaRestriction_section lower upper length lowerPositive upperPositive upperBounded lengthPositive included field mode)
  change highPowerCurve upper highTiltExponent upperPositive radius.val •
    (annularInversePhase parameters mode.val.2 radius.val • (_ : ComplexEuclidean 1)) =
    highPowerCurve lower highTiltExponent lowerPositive radius.val •
      (annularInversePhase parameters mode.val.2 radius.val • (_ : ComplexEuclidean 1))
  exact congrArg₂ (fun (factor : ℝ) (value : ComplexEuclidean 1) => factor •
    (annularInversePhase parameters mode.val.2 radius.val • value))
    ((highPowerCurve_physical upper highTiltExponent upperPositive radius.val radius.property).trans
      (highPowerCurve_physical lower highTiltExponent lowerPositive radius.val
        ⟨included.trans radius.property.1, radius.property.2⟩).symm) same

end Grad.AnnularRestriction
