import AKG6ActualNewEndpointDatum

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open Set
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularFluxTrace Grad.AnnularOmegaGraph
open Grad.AnnularCurrentSource Grad.AnnularCurrentBoundary Grad.AnnularCrossMaps Grad.AnnularLowEnergy
open Grad.AnnularTiltedReference Grad.AnnularForwardTraces Grad.BoundaryKernelAction
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Actual completed source H1 outer trace, proved from the SAME dense core. -/
theorem sourceRadialRestriction_outerTrace (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (field : WeightedRadialH1 dimension lower) :
    weightedRadialTrace dimension upper upperPositive upperBounded 1
      (sourceRadialRestriction dimension lower upper included field) =
    weightedRadialTrace dimension lower lowerPositive (included.trans_lt upperBounded) 1 field := by
  apply isClosed_property (weightedRadialCoreInto_denseRange dimension lower)
    (isClosed_eq
      ((weightedRadialTrace dimension upper upperPositive upperBounded 1).continuous.comp
        (sourceRadialRestriction dimension lower upper included).continuous)
      (weightedRadialTrace dimension lower lowerPositive (included.trans_lt upperBounded) 1).continuous) _ field
  intro core
  dsimp only [Function.comp_apply]
  rw [sourceRadialRestriction_core,weightedRadialTrace_core,weightedRadialTrace_core]
  rfl

theorem sourceGraphRestriction_outerTrace (parameters : PhaseParameters) (dimension : ℕ)
    (lower upper : ℝ) (included : lower ≤ upper) (lowerPositive : 0 < lower) (upperPositive : 0 < upper)
    (upperBounded : upper < 1) (angular cell grade : ℕ)
    (field : AnnularTotalSourceH1 parameters dimension lower angular cell grade) :
    totalSourceTrace parameters dimension upper upperPositive upperBounded angular cell grade 1
      (sourceGraphRestriction parameters dimension lower upper included angular cell grade field) =
    totalSourceTrace parameters dimension lower lowerPositive (included.trans_lt upperBounded) angular cell grade 1 field := by
  apply lp.ext
  funext mode
  exact sourceRadialRestriction_outerTrace dimension lower upper included lowerPositive upperPositive upperBounded (field mode)

theorem sourceGraphRestriction_rotationTrace (parameters : PhaseParameters) (dimension : ℕ)
    (lower upper : ℝ) (included : lower ≤ upper) (lowerPositive : 0 < lower) (upperPositive : 0 < upper)
    (upperBounded : upper < 1) (cell grade : ℕ)
    (field : AnnularTotalSourceH1 parameters dimension lower 1 cell grade) :
    sourceRotationTrace parameters dimension upper upperPositive upperBounded cell grade 1
      (sourceGraphRestriction parameters dimension lower upper included 1 cell grade field) =
    sourceRotationTrace parameters dimension lower lowerPositive (included.trans_lt upperBounded) cell grade 1 field := by
  change totalEndpointAngular parameters dimension 1 cell grade
    (totalSourceTrace parameters dimension upper upperPositive upperBounded 1 cell grade 1
      (sourceGraphRestriction parameters dimension lower upper included 1 cell grade field)) =
    totalEndpointAngular parameters dimension 1 cell grade
      (totalSourceTrace parameters dimension lower lowerPositive (included.trans_lt upperBounded) 1 cell grade 1 field)
  rw [sourceGraphRestriction_outerTrace]

/-- The full copied F0/RF0/F2 outer tuple is unchanged, with RF0 from the SAME F0 graph. -/
theorem originalSourceGraphPairRestriction_outerTuple (parameters : PhaseParameters) (lower upper : ℝ)
    (included : lower ≤ upper) (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (graphs : HighKnownGraphHilbert parameters lower) :
    highGraphOuterTuple parameters upper upperPositive upperBounded 0
      (originalSourceGraphPairRestriction parameters lower upper included graphs).ofLp =
    highGraphOuterTuple parameters lower lowerPositive (included.trans_lt upperBounded) 0 graphs.ofLp := by
  apply PiLp.ext
  intro slot
  fin_cases slot
  · change annularEndpointInclusion parameters 1 1 0 0 1 0 _ _
      (totalSourceTrace parameters 1 upper upperPositive upperBounded 1 0 0 1
        (sourceGraphRestriction parameters 1 lower upper included 1 0 0 graphs.ofLp.1)) =
      annularEndpointInclusion parameters 1 1 0 0 1 0 _ _
        (totalSourceTrace parameters 1 lower lowerPositive (included.trans_lt upperBounded) 1 0 0 1 graphs.ofLp.1)
    rw [sourceGraphRestriction_outerTrace]
  · exact sourceGraphRestriction_rotationTrace parameters 1 lower upper included lowerPositive upperPositive upperBounded 0 0 graphs.ofLp.1
  · exact sourceGraphRestriction_outerTrace parameters 1 lower upper included lowerPositive upperPositive upperBounded 0 0 0 graphs.ofLp.2

theorem highOmegaRestriction_outerTrace (lower upper length : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper)
    (field : annularOmegaGraph lower length lowerPositive lengthPositive) :
    annularFluxTrace upper upperPositive upperBounded 1
      (annularOmegaIntoNu upper length upperPositive lengthPositive
        (highOmegaRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field)) =
    annularFluxTrace lower lowerPositive (included.trans_lt upperBounded) 1
      (annularOmegaIntoNu lower length lowerPositive lengthPositive field) := by
  apply lp.ext
  funext mode
  rw [annularFluxTrace_apply,annularFluxTrace_apply]
  have same := congrArg (fun representative : RadialContinuousSection 1 upper =>
    representative ⟨1,upperBounded.le,le_rfl⟩)
      (highOmegaRestriction_section lower upper length lowerPositive upperPositive upperBounded lengthPositive included field mode)
  exact congrArg (fun value : ComplexEuclidean 1 =>
    (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2))⁻¹ • value) same

theorem highEnergyRestriction_actualOuter (parameters : PhaseParameters) (lower upper length : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperHalf : upper ≤ 1 / 2)
    (lengthPositive : 0 < length) (included : lower ≤ upper) (field : annularEnergySpace lower length lowerPositive) :
    actualCurrentHighOuterTrace parameters upper length upperPositive upperHalf lengthPositive 0 0
      (highEnergyRestriction lower upper length lowerPositive upperPositive included field) =
    actualCurrentHighOuterTrace parameters lower length lowerPositive (included.trans upperHalf) lengthPositive 0 0 field := by
  rw [actualCurrentHighOuterTrace_same,actualCurrentHighOuterTrace_same,
    ← highEnergyRestriction_bDecode lower upper length lowerPositive upperPositive (upperHalf.trans_lt (by norm_num)) included,
    highEnergyRestriction_outerTrace]

end Grad.AnnularRestriction
