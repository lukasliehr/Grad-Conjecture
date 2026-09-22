import AJZ6OriginalFullSourceBlockContraction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000
open Set Filter MeasureTheory
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.AnnularSourceGraph
open Grad.AnnularVariational Grad.AnnularStrongData Grad.AnnularCurrentSource

/-- Exact full AK31 source consumer: original F0/F2 value AND derivative,
full F1/strengthened G3 bulk, and the norm-one estimate. -/
theorem originalFullSourceRestriction_exact (parameters : PhaseParameters) (lower upper : ℝ) (included : lower ≤ upper)
    (field : WithLp 2 (HighKnownGraphHilbert parameters lower × WithLp 2 (DivisionRow 1 lower × DivisionRow 1 lower))) :
    let output := originalFullSourceRestriction parameters lower upper included field
    (∀ slot : Fin 2,
      annularSourceCoordinate parameters 1 upper 1 0 slot output.ofLp.1.ofLp.1 =
        originalBulkRestriction 1 lower upper included (annularSourceCoordinate parameters 1 lower 1 0 slot field.ofLp.1.ofLp.1)) ∧
    (∀ slot : Fin 2,
      annularSourceCoordinate parameters 1 upper 0 0 slot output.ofLp.1.ofLp.2 =
        originalBulkRestriction 1 lower upper included (annularSourceCoordinate parameters 1 lower 0 0 slot field.ofLp.1.ofLp.2)) ∧
    output.ofLp.2.ofLp.1 = originalBulkRestriction 1 lower upper included field.ofLp.2.ofLp.1 ∧
    output.ofLp.2.ofLp.2 = originalBulkRestriction 1 lower upper included field.ofLp.2.ofLp.2 ∧
    ‖output‖ ≤ ‖field‖ :=
  ⟨sourceGraphRestriction_coordinate parameters 1 lower upper included 1 0 0 field.ofLp.1.ofLp.1,
    sourceGraphRestriction_coordinate parameters 1 lower upper included 0 0 0 field.ofLp.1.ofLp.2,
    rfl, rfl, originalFullSourceRestriction_bound parameters lower upper included field⟩

theorem originalFullSourceRestriction_inserted (parameters : PhaseParameters) (lower upper : ℝ) (included : lower ≤ upper)
    (grade : ℕ)
    (field weighted : WithLp 2 (HighKnownGraphHilbert parameters lower × WithLp 2 (DivisionRow 1 lower × DivisionRow 1 lower)))
    (first : ∀ mode : ℤ × ℤ, weighted.ofLp.1.ofLp.1 mode =
      Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade • field.ofLp.1.ofLp.1 mode)
    (second : ∀ mode : ℤ × ℤ, weighted.ofLp.1.ofLp.2 mode =
      Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade • field.ofLp.1.ofLp.2 mode)
    (third : ∀ mode : ℤ × ℤ, weighted.ofLp.2.ofLp.1 mode =
      Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade • field.ofLp.2.ofLp.1 mode)
    (fourth : ∀ mode : ℤ × ℤ, weighted.ofLp.2.ofLp.2 mode =
      Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade • field.ofLp.2.ofLp.2 mode) :
    let output := originalFullSourceRestriction parameters lower upper included field
    let inserted := originalFullSourceRestriction parameters lower upper included weighted
    (∀ mode : ℤ × ℤ, inserted.ofLp.1.ofLp.1 mode =
      Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade • output.ofLp.1.ofLp.1 mode) ∧
    (∀ mode : ℤ × ℤ, inserted.ofLp.1.ofLp.2 mode =
      Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade • output.ofLp.1.ofLp.2 mode) ∧
    (∀ mode : ℤ × ℤ, inserted.ofLp.2.ofLp.1 mode =
      Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade • output.ofLp.2.ofLp.1 mode) ∧
    (∀ mode : ℤ × ℤ, inserted.ofLp.2.ofLp.2 mode =
      Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade • output.ofLp.2.ofLp.2 mode) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sourceGraphRestriction_inserted parameters 1 lower upper included 1 0 grade _ _ first
  · exact sourceGraphRestriction_inserted parameters 1 lower upper included 0 0 grade _ _ second
  · intro mode
    change collarL2Restriction 1 lower upper included (weighted.ofLp.2.ofLp.1 mode) = _
    rw [third, (collarL2Restriction 1 lower upper included).map_smul_of_tower]
    rfl
  · intro mode
    change collarL2Restriction 1 lower upper included (weighted.ofLp.2.ofLp.2 mode) = _
    rw [fourth, (collarL2Restriction 1 lower upper included).map_smul_of_tower]
    rfl

theorem originalFullSourceRestriction_sourcePhysical (parameters : PhaseParameters) (lower upper : ℝ)
    (included : lower ≤ upper) (positiveLower : 0 < lower) (positiveUpper : 0 < upper) (bounded : upper ≤ 1)
    (field : WithLp 2 (HighKnownGraphHilbert parameters lower × WithLp 2 (DivisionRow 1 lower × DivisionRow 1 lower))) :
    let output := originalFullSourceRestriction parameters lower upper included field
    ∀ᵐ radius ∂volume.restrict (Icc upper 1), ∀ mode : ℤ × ℤ,
      totalSourceCoefficient parameters 1 upper positiveUpper bounded 1 0 0 output.ofLp.1.ofLp.1 mode radius =
        totalSourceCoefficient parameters 1 lower positiveLower (included.trans bounded) 1 0 0 field.ofLp.1.ofLp.1 mode radius ∧
      totalSourceCoefficient parameters 1 upper positiveUpper bounded 0 0 0 output.ofLp.1.ofLp.2 mode radius =
        totalSourceCoefficient parameters 1 lower positiveLower (included.trans bounded) 0 0 0 field.ofLp.1.ofLp.2 mode radius := by
  filter_upwards [sourceGraphRestriction_physical parameters 1 lower upper included positiveLower positiveUpper bounded
    1 0 0 field.ofLp.1.ofLp.1,
    sourceGraphRestriction_physical parameters 1 lower upper included positiveLower positiveUpper bounded
    0 0 0 field.ofLp.1.ofLp.2] with radius first second
  intro mode
  exact ⟨first mode, second mode⟩

/-- Exactly the three original mean-free source/residual supports survive;
the F0 source is allowed to retain its angular mean. -/
theorem originalFullSourceRestriction_meanFree (parameters : PhaseParameters) (lower upper : ℝ) (included : lower ≤ upper)
    (field : WithLp 2 (HighKnownGraphHilbert parameters lower × WithLp 2 (DivisionRow 1 lower × DivisionRow 1 lower)))
    (first : ∀ mode : ℤ × ℤ, mode.1 = 0 → unweightedSourceF2Bulk parameters lower field.ofLp.1.ofLp.2 mode = 0)
    (second : ∀ mode : ℤ × ℤ, mode.1 = 0 → field.ofLp.2.ofLp.1 mode = 0)
    (third : ∀ mode : ℤ × ℤ, mode.1 = 0 → field.ofLp.2.ofLp.2 mode = 0) :
    let output := originalFullSourceRestriction parameters lower upper included field
    (∀ mode : ℤ × ℤ, mode.1 = 0 → unweightedSourceF2Bulk parameters upper output.ofLp.1.ofLp.2 mode = 0) ∧
    (∀ mode : ℤ × ℤ, mode.1 = 0 → output.ofLp.2.ofLp.1 mode = 0) ∧
    (∀ mode : ℤ × ℤ, mode.1 = 0 → output.ofLp.2.ofLp.2 mode = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro mode zero
    change unweightedSourceF2Bulk parameters upper
      (sourceGraphRestriction parameters 1 lower upper included 0 0 0 field.ofLp.1.ofLp.2) mode = 0
    rw [← originalBulkRestriction_F2]
    change collarL2Restriction 1 lower upper included
      (unweightedSourceF2Bulk parameters lower field.ofLp.1.ofLp.2 mode) = 0
    rw [first mode zero, map_zero]
  · intro mode zero
    change collarL2Restriction 1 lower upper included (field.ofLp.2.ofLp.1 mode) = 0
    rw [second mode zero, map_zero]
  · intro mode zero
    change collarL2Restriction 1 lower upper included (field.ofLp.2.ofLp.2 mode) = 0
    rw [third mode zero, map_zero]

end Grad.AnnularRestriction
