import SD1Fields

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (CellValues PhysicalValue FieldL2)
open Grad.WeightedJets (JetIndex degree derivativeWord base)
open Grad.SpatialDilation (disk)
open Grad.Mollifier.Pointwise (orderedDerivative smoothRepresentative scaledEta)
open scoped ContDiff Topology BigOperators

namespace Grad.SmoothDensity

set_option maxHeartbeats 1600000

theorem stepJet_coordinates (dimension : ℕ) (radius : ℝ) (positiveRadius : 0 < radius)
    (grade : Grade) (step : Step radius) (jet : Jet dimension (disk radius) grade) :
    ∀ᵐ point ∂volume, ∀ (index : JetIndex grade.order) (cell : ℤ),
      (stepJet dimension radius positiveRadius grade step jet).val index point cell =
        Grad.CellWeights.positiveFactor (grade.exponent index) cell •
          orderedDerivative (degree index) (derivativeWord index)
            (stepFunction dimension radius positiveRadius step (jetBase dimension (disk radius) grade jet)) point cell := by
  let extended := extendedJet dimension radius positiveRadius grade step jet
  let prepared := preparedField dimension radius positiveRadius step (jetBase dimension (disk radius) grade jet)
  let function := smoothRepresentative (CellValues dimension) (scaledEta step.epsilon) prepared
  let cells := Grad.WeightedJets.CellCutoff.centeredCells step.cellRadius
  let projection := Grad.CellProjections.Generic.projection (PhysicalValue dimension) cells
  have smooth : ContDiff ℝ ∞ function :=
    (Grad.Mollifier.Pointwise.pointwiseGoal (CellValues dimension) _
      (Grad.Mollifier.Pointwise.scaledEta_contDiff step.epsilon)
      (Grad.Mollifier.Pointwise.scaledEta_compactSupport step.epsilon step.positiveEpsilon) prepared).2.1
  have represented : ∀ᵐ point ∂volume, ∀ index : JetIndex grade.order,
      (regularizedJet dimension radius positiveRadius grade step jet).val index point =
        smoothRepresentative (CellValues dimension) (scaledEta step.epsilon) (extended.val index) point := by
    apply ae_all_iff.mpr
    intro index
    change (Grad.Mollifier.WeakJets.Consumer.weightedRegularizer dimension grade.order grade.exponent
      step.epsilon extended).val index =ᵐ[volume] _
    rw [Grad.Mollifier.WeakJets.Consumer.weightedCoordinate _ _ _ _ step.positiveEpsilon]
    exact (Grad.Mollifier.WeakJets.average_realization (CellValues dimension) _
      (Grad.Mollifier.Pointwise.scaledEta_integrable step.epsilon step.positiveEpsilon) (extended.val index)).1
  have projected := Grad.SpatialTranslation.ae_univ_iff.mp
    (Grad.WeightedJets.CellCutoff.cutoff_coordinates dimension grade.order Set.univ grade.exponent cells
      (regularizedJet dimension radius positiveRadius grade step jet))
  filter_upwards [represented, projected] with point regularizedAt projectedAt
  intro index cell
  have kernel := Grad.Mollifier.WeakJets.Consumer.smoothAllCells dimension grade.order grade.exponent
    step.epsilon step.positiveEpsilon extended index point cell
  have sameBase : base dimension grade.order Set.univ grade.exponent extended = prepared :=
    extendedJet_base dimension radius positiveRadius grade step jet
  rw [sameBase] at kernel
  change (Grad.WeightedJets.CellCutoff.cutoff dimension grade.order Set.univ grade.exponent cells
    (regularizedJet dimension radius positiveRadius grade step jet)).val index point cell = _
  rw [projectedAt index cell, regularizedAt index]
  change (if cell ∈ cells then _ else 0) =
    Grad.CellWeights.positiveFactor (grade.exponent index) cell •
      orderedDerivative (degree index) (derivativeWord index) (fun source => projection (function source)) point cell
  have derivativeMap := congrArg (fun value : CellValues dimension => value cell)
    (orderedDerivative_map projection (degree index) (derivativeWord index) function smooth point)
  have literal := derivativeMap.trans
    (Grad.CellProjections.Generic.projection_coordinate (PhysicalValue dimension) cells
      (orderedDerivative (degree index) (derivativeWord index) function point) cell)
  refine Eq.trans ?_ (congrArg (fun value : PhysicalValue dimension =>
    Grad.CellWeights.positiveFactor (grade.exponent index) cell • value) literal.symm)
  rw [kernel]
  split_ifs
  · rfl
  · simp only [smul_zero]

theorem stepJet_realizes (dimension : ℕ) (radius : ℝ) (positiveRadius : 0 < radius)
    (grade : Grade) (step : Step radius) (jet : Jet dimension (disk radius) grade) :
    Realizes dimension Set.univ grade
      (stepFunction dimension radius positiveRadius step (jetBase dimension (disk radius) grade jet))
      (stepJet dimension radius positiveRadius grade step jet) := by
  constructor
  · rw [stepJet_base]
    exact Grad.SpatialTranslation.ae_univ_iff.mpr (stepField_ae dimension radius positiveRadius step _)
  · exact Grad.SpatialTranslation.ae_univ_iff.mpr (stepJet_coordinates dimension radius positiveRadius grade step jet)

theorem realizes_restriction (dimension : ℕ) {smaller larger : Set Spatial} (inclusion : smaller ⊆ larger)
    (measurableLarger : MeasurableSet larger) (grade : Grade) (function : Spatial → CellValues dimension)
    (jet : Jet dimension larger grade) (realized : Realizes dimension larger grade function jet) :
    Realizes dimension smaller grade function
      (Grad.WeightedJets.Restriction.restriction dimension grade.order inclusion measurableLarger grade.exponent jet) := by
  constructor
  · change Grad.WeightedJets.base dimension grade.order smaller grade.exponent _ =ᵐ[volume.restrict smaller] _
    rw [Grad.WeightedJets.Restriction.restriction_base]
    exact (Grad.WeightedJets.Restriction.fieldRestriction_ae (CellValues dimension) inclusion _).trans
      (ae_mono (Measure.restrict_mono inclusion le_rfl) realized.1)
  · filter_upwards [Grad.WeightedJets.Restriction.restriction_coordinates dimension grade.order inclusion
      measurableLarger grade.exponent jet, ae_mono (Measure.restrict_mono inclusion le_rfl) realized.2]
      with point restrictedAt originalAt
    intro index cell
    exact (restrictedAt index cell).trans (originalAt index cell)

theorem realizes_recovery (dimension : ℕ) (domain : Set Spatial) (grade : Grade)
    (function : Spatial → CellValues dimension) (jet : Jet dimension domain grade)
    (realized : Realizes dimension domain grade function jet) (index : JetIndex grade.order) :
    Grad.WeightedJets.Realization.recoveredDerivative dimension grade.order domain grade.exponent index jet
      =ᵐ[volume.restrict domain] orderedDerivative (degree index) (derivativeWord index) function := by
  filter_upwards [Grad.CellWeights.inverseFieldCLM_coordinate dimension domain (grade.exponent index)
    (jet.val index), realized.2] with point inverseAt originalAt
  apply lp.ext
  funext cell
  change Grad.CellWeights.inverseFieldCLM dimension domain (grade.exponent index) (jet.val index) point cell = _
  rw [inverseAt cell, originalAt index cell, smul_smul,
    Grad.Mollifier.WeakJets.inverse_positive_cancel, one_smul]

theorem realizes_integral (dimension : ℕ) (domain : Set Spatial) (grade : Grade)
    (function : Spatial → CellValues dimension) (jet : Jet dimension domain grade)
    (realized : Realizes dimension domain grade function jet) (index : JetIndex grade.order)
    (cell : ℤ) (vector : PhysicalValue dimension) (test : Grad.WeightedJets.TestFunction domain) :
    (∫ point in domain, test.toFun point • inner ℂ vector
      (orderedDerivative (degree index) (derivativeWord index) function point cell)) =
        (-1 : ℂ) ^ degree index * ∫ point in domain,
          Grad.WeakTesting.orderedTestDerivative (degree index) (derivativeWord index) test.toFun point •
            inner ℂ vector (function point cell) := by
  have identity := Grad.WeightedJets.Realization.recoveredDerivative_weak dimension grade.order domain
    grade.exponent index jet cell vector test
  rw [Grad.WeightedJets.testPairing_apply, Grad.WeightedJets.derivativeTestPairing_apply] at identity
  have derivativeEquality := realizes_recovery dimension domain grade function jet realized index
  calc
    _ = ∫ point in domain, test.toFun point • inner ℂ vector
        (Grad.WeightedJets.Realization.recoveredDerivative dimension grade.order domain grade.exponent index jet point cell) := by
      apply integral_congr_ae
      filter_upwards [derivativeEquality] with point equality
      rw [equality]
    _ = _ := identity.trans (congrArg (fun value : ℂ => (-1 : ℂ) ^ degree index * value) (by
      apply integral_congr_ae
      filter_upwards [realized.1] with point equality
      rw [← jetBase, equality]))

theorem realizes_norm (dimension : ℕ) (grade : Grade) (function : Spatial → CellValues dimension)
    (cells : Finset ℤ) (core : CoreLaws dimension function cells) (jet : Jet dimension Set.univ grade)
    (realized : Realizes dimension Set.univ grade function jet) :
    ‖jet‖ ^ 2 = ∑ index : JetIndex grade.order,
      (eLpNorm (weightedDerivative dimension (grade.exponent index) (degree index) (derivativeWord index)
        cells function) 2 volume).toReal ^ 2 := by
  rw [Grad.WeightedJets.jet_norm_sq]
  apply Finset.sum_congr rfl
  intro index _membership
  have representation : jet.val index =ᵐ[volume]
      weightedDerivative dimension (grade.exponent index) (degree index) (derivativeWord index) cells function := by
    filter_upwards [Grad.SpatialTranslation.ae_univ_iff.mp realized.2] with point coordinates
    apply lp.ext
    funext cell
    exact (coordinates index cell).trans
      ((higher_finite_goal dimension function cells core (grade.exponent index) (degree index)
        (derivativeWord index)).2.2.2 point cell).symm
  rw [Lp.norm_def]
  apply congrArg (fun value : ENNReal => value.toReal ^ 2)
  exact (congrArg (fun measure : Measure Spatial =>
    eLpNorm (jet.val index : Spatial → CellValues dimension) 2 measure) (Measure.restrict_univ)).trans
    (eLpNorm_congr_ae representation)

theorem stage_goal : StageGoal := by
  intro dimension radius positiveRadius step field
  refine ⟨stepFunction_core dimension radius positiveRadius step field,
    stepField_ae dimension radius positiveRadius step field, ?_⟩
  intro grade jet sameBase
  subst field
  have realized := stepJet_realizes dimension radius positiveRadius grade step jet
  have restricted := realizes_restriction dimension (Set.subset_univ (disk radius)) MeasurableSet.univ
    grade _ _ realized
  exact ⟨dilatedJet_base dimension radius grade step jet,
    extendedJet_base dimension radius positiveRadius grade step jet,
    regularizedJet_base dimension radius positiveRadius grade step jet,
    stepJet_base dimension radius positiveRadius grade step jet, realized, restricted,
    realizes_norm dimension grade _ _ (stepFunction_core dimension radius positiveRadius step _) _ realized,
    realizes_integral dimension (disk radius) grade _ _ restricted⟩

end Grad.SmoothDensity
