import AJE17ExactFullKnownFunctionalOrbit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularKernelL2

theorem sourceHighRow_translation (lower : ℝ) (tau : OrbitParameter) (field : DivisionRow 1 lower) :
    highRowProjection lower (orbitLpAction (RadialL2 1 lower) tau field) =
      orbitLpAction (RadialL2 1 lower) tau (highRowProjection lower field) := by
  apply lp.ext
  funext mode
  by_cases high : 3 ≤ |mode.1|
  · rw [highRowProjection_high lower _ ⟨mode,high⟩]
    change orbitCharacter tau mode • field mode = orbitCharacter tau mode • highRowProjection lower field mode
    exact congrArg (fun value : RadialL2 1 lower => orbitCharacter tau mode • value)
      (highRowProjection_high lower field ⟨mode,high⟩).symm
  · rw [highRowProjection_low lower _ mode high]
    change 0 = orbitCharacter tau mode • highRowProjection lower field mode
    rw [highRowProjection_low lower field mode high,smul_zero]

private theorem strongHighWeighted_translation (lower : ℝ) (tau : OrbitParameter)
    (field : HighKnownSourceBulk lower) :
    strongHighWeightedMap lower (WithLp.toLp 2 (fun slot => orbitLpAction (RadialL2 1 lower) tau (field slot))) =
      WithLp.toLp 2 (fun slot => orbitLpAction (RadialL2 1 lower) tau (strongHighWeightedMap lower field slot)) := by
  apply PiLp.ext
  intro slot
  fin_cases slot
  · rfl
  · rfl
  · rfl
  · exact sourceHighRow_translation lower tau (field 3)

private theorem strongHighAuxiliary_translation (lower : ℝ) (tau : OrbitParameter)
    (field : HighAuxiliarySourceBulk lower) :
    strongHighAuxiliaryMap lower (WithLp.toLp 2 (fun slot => orbitLpAction (RadialL2 1 lower) tau (field slot))) =
      WithLp.toLp 2 (fun slot => orbitLpAction (RadialL2 1 lower) tau (strongHighAuxiliaryMap lower field slot)) := by
  apply PiLp.ext
  intro slot
  fin_cases slot
  · exact sourceHighRow_translation lower tau (field 0)
  · exact (map_zero (orbitLpAction (RadialL2 1 lower) tau)).symm
  · exact (map_zero (orbitLpAction (RadialL2 1 lower) tau)).symm

theorem strongHighAmbientMap_translation (parameters : PhaseParameters) (lower : ℝ) (angular cell : ℕ)
    (tau : OrbitParameter) (data : ActualHighKnownAmbient parameters lower angular cell) :
    strongHighAmbientMap parameters lower angular cell
      (highKnownAmbientTranslation parameters lower angular cell tau data) =
    highKnownAmbientTranslation parameters lower angular cell tau
      (strongHighAmbientMap parameters lower angular cell data) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
  apply Prod.ext
  · change strongHighBulkMap lower (highKnownAmbientTranslation parameters lower angular cell tau data).ofLp.1 =
      (highKnownAmbientTranslation parameters lower angular cell tau
        (strongHighAmbientMap parameters lower angular cell data)).ofLp.1
    apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
    exact Prod.ext (strongHighWeighted_translation lower tau data.ofLp.1.ofLp.1)
      (strongHighAuxiliary_translation lower tau data.ofLp.1.ofLp.2)
  · rfl

/-- High and low consumers receive the same simultaneous translated original
strong datum; only the prescribed high restriction of f and g is performed. -/
theorem strongToHigh_translation (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (angular cell : ℕ) (tau : OrbitParameter)
    (data : StrongDataCarrier parameters lower positive bounded angular cell) :
    (strongToHigh parameters lower positive bounded angular cell
      (strongDataTranslation parameters lower positive bounded angular cell tau data)).val =
    highKnownAmbientTranslation parameters lower angular cell tau
      (strongToHigh parameters lower positive bounded angular cell data).val :=
  strongHighAmbientMap_translation parameters lower angular cell tau data.val.ofLp.1

end Grad.AnnularStrongOrbit
