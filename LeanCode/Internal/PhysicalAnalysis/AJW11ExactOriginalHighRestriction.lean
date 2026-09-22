import AJW10SameHighPhysicalFields
import AED5ExactTraceTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
open Set
open scoped Topology
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.AnnularOmegaGraph
open Grad.AnnularHighTilt Grad.AnnularTiltedReference Grad.AnnularCrossMaps Grad.AnnularOriginalHigh Grad.AnnularGrades

theorem restrictionPairMap_range_iff {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (first : E →L[ℂ] G) (second : F →L[ℂ] H) (field : WithLp 2 (G × H)) :
    field ∈ LinearMap.range (restrictionPairMap first second).toLinearMap ↔
      (∃ energy, first energy = field.ofLp.1) ∧ (∃ flux, second flux = field.ofLp.2) := by
  constructor
  · rintro ⟨weighted, rfl⟩
    exact ⟨⟨weighted.ofLp.1, rfl⟩, ⟨weighted.ofLp.2, rfl⟩⟩
  · rintro ⟨⟨energy, sameEnergy⟩, ⟨flux, sameFlux⟩⟩
    refine ⟨(WithLp.prodContinuousLinearEquiv 2 ℂ E F).symm (energy, flux), ?_⟩
    apply (WithLp.prodContinuousLinearEquiv 2 ℂ G H).injective
    exact Prod.ext sameEnergy sameFlux

theorem originalHighGradeDecode_range_iff (lower length : ℝ) (positive : 0 < lower)
    (angular cell inserted : ℕ) (field : OriginalHighSpace lower length positive) :
    field ∈ LinearMap.range (originalHighGradeDecode lower length positive angular cell inserted).toLinearMap ↔
      HasAnnularEnergyGrade lower length positive angular cell inserted field.ofLp.1 ∧
      HasAnnularFluxGrade lower positive angular cell inserted (originalNuPairEquivalence lower positive field.ofLp.2) :=
  (restrictionPairMap_range_iff (annularEnergyDecode lower length positive angular cell inserted)
    (originalNuDecode lower positive angular cell inserted) field).trans
    (and_congr (annularEnergyDecode_range_iff lower length positive angular cell inserted field.ofLp.1)
      (originalNuGrade_iff lower positive angular cell inserted field.ofLp.2).symm)

variable (lower upper length : ℝ) (lowerPositive : 0 < lower) (upperPositive : 0 < upper)
    (upperBounded : upper < 1) (lengthPositive : 0 < length) (included : lower ≤ upper)

theorem highOmegaRestriction_coordinates (field : annularOmegaGraph lower length lowerPositive lengthPositive)
    (slot : Fin 2) (mode : HighAnnularMode) :
    (highOmegaRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field).val slot mode =
      collarL2Restriction 1 lower upper included (field.val slot mode) := rfl

theorem originalHighRestriction_hasGrade (angular cell inserted : ℕ)
    (field : OriginalHighSpace lower length lowerPositive)
    (energy : HasAnnularEnergyGrade lower length lowerPositive angular cell inserted field.ofLp.1)
    (flux : HasAnnularFluxGrade lower lowerPositive angular cell inserted (originalNuPairEquivalence lower lowerPositive field.ofLp.2)) :
    let output := originalHighRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field
    HasAnnularEnergyGrade upper length upperPositive angular cell inserted output.ofLp.1 ∧
      HasAnnularFluxGrade upper upperPositive angular cell inserted (originalNuPairEquivalence upper upperPositive output.ofLp.2) :=
  (originalHighGradeDecode_range_iff upper length upperPositive angular cell inserted _).mp
    (originalHighRestriction_gradeRange lower upper length lowerPositive upperPositive upperBounded lengthPositive included angular cell inserted field
      ((originalHighGradeDecode_range_iff lower length lowerPositive angular cell inserted field).mpr ⟨energy, flux⟩))

/-- Original outer scalar trace remains the same after the actual endpoint conjugation. -/
theorem originalHighRestriction_outerTrace (field : OriginalHighSpace lower length lowerPositive) :
    annularEnergyTrace upper length upperPositive upperBounded lengthPositive 1
      (originalHighRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field).ofLp.1 =
    annularEnergyTrace lower length lowerPositive (included.trans_lt upperBounded) lengthPositive 1 field.ofLp.1 := by
  change annularEnergyTrace upper length upperPositive upperBounded lengthPositive 1
    (highEnergyUnweight upper length upperPositive upperBounded.le
      (highEnergyRestriction lower upper length lowerPositive upperPositive included
        (highEnergyWeight lower length lowerPositive (included.trans upperBounded.le) field.ofLp.1))) = _
  exact (highEnergyUnweight_outerTrace upper length upperPositive upperBounded lengthPositive _).trans
    ((highEnergyRestriction_outerTrace lower upper length lowerPositive upperPositive upperBounded lengthPositive included _).trans
      (highEnergyWeight_outerTrace lower length lowerPositive (included.trans_lt upperBounded) lengthPositive field.ofLp.1))

/-- Both original physical fields agree at every point, including the new incoming endpoint. -/
theorem originalHighRestriction_physical (parameters : PhaseParameters)
    (field : OriginalHighSpace lower length lowerPositive) (mode : HighAnnularMode) (radius : Icc upper (1 : ℝ)) :
    let output := originalHighTiltEquivalence upper length upperPositive upperBounded.le lengthPositive
      (originalHighRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field)
    let input := originalHighTiltEquivalence lower length lowerPositive (included.trans upperBounded.le) lengthPositive field
    (weightedHighXiPhysicalSection parameters upper length upperPositive upperBounded output.ofLp.1 mode radius =
      weightedHighXiPhysicalSection parameters lower length lowerPositive (included.trans_lt upperBounded) input.ofLp.1 mode
        ⟨radius.val, included.trans radius.property.1, radius.property.2⟩) ∧
    (weightedHighXPhysicalSection parameters upper length upperPositive upperBounded lengthPositive output.ofLp.2 mode radius =
      weightedHighXPhysicalSection parameters lower length lowerPositive (included.trans_lt upperBounded) lengthPositive input.ofLp.2 mode
        ⟨radius.val, included.trans radius.property.1, radius.property.2⟩) := by
  let input := originalHighTiltEquivalence lower length lowerPositive (included.trans upperBounded.le) lengthPositive field
  have same := originalHighRestriction_weighted lower upper length lowerPositive upperPositive upperBounded lengthPositive included field
  have first := congrArg (fun pair : CrossHighSpace upper length upperPositive lengthPositive =>
    weightedHighXiPhysicalSection parameters upper length upperPositive upperBounded pair.ofLp.1 mode radius) same
  have second := congrArg (fun pair : CrossHighSpace upper length upperPositive lengthPositive =>
    weightedHighXPhysicalSection parameters upper length upperPositive upperBounded lengthPositive pair.ofLp.2 mode radius) same
  exact ⟨first.trans (highEnergyRestriction_physical lower upper length lowerPositive upperPositive upperBounded included parameters input.ofLp.1 mode radius),
    second.trans (highOmegaRestriction_physical lower upper length lowerPositive upperPositive upperBounded lengthPositive included parameters input.ofLp.2 mode radius)⟩

/-- Immediate retained high V1 consumer: exact original endpoint conjugation,
weighted contraction, fixed-endpoint original continuity, and unchanged outer trace. -/
theorem originalHighEndpointRestriction_exact (field : OriginalHighSpace lower length lowerPositive) :
    let input := originalHighTiltEquivalence lower length lowerPositive (included.trans upperBounded.le) lengthPositive field
    let output := originalHighRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field
    originalHighTiltEquivalence upper length upperPositive upperBounded.le lengthPositive output =
      highWeightedRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included input ∧
    ‖highWeightedRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included input‖ ≤ ‖input‖ ∧
    ‖output‖ ≤
      (‖(originalHighTiltEquivalence upper length upperPositive upperBounded.le lengthPositive).symm.toContinuousLinearMap‖ *
        ‖(originalHighTiltEquivalence lower length lowerPositive (included.trans upperBounded.le) lengthPositive).toContinuousLinearMap‖) * ‖field‖ ∧
    annularEnergyTrace upper length upperPositive upperBounded lengthPositive 1 output.ofLp.1 =
      annularEnergyTrace lower length lowerPositive (included.trans_lt upperBounded) lengthPositive 1 field.ofLp.1 := by
  dsimp only
  exact ⟨originalHighRestriction_weighted lower upper length lowerPositive upperPositive upperBounded lengthPositive included field,
    highWeightedRestriction_bound lower upper length lowerPositive upperPositive upperBounded lengthPositive included _,
    originalHighRestriction_bound lower upper length lowerPositive upperPositive upperBounded lengthPositive included field,
    originalHighRestriction_outerTrace lower upper length lowerPositive upperPositive upperBounded lengthPositive included field⟩

end Grad.AnnularRestriction
