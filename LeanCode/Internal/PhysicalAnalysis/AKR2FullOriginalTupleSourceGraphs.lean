import AKR1GenuineWeightedTupleRadialGraphs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularOriginalSmoothCore
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (tuple : OriginalSmoothTuple parameters lower) (slot : Fin 4)

theorem tupleConjugatedJet_summable (order grade : ℕ) :
    Summable (fun mode : ℤ × ℤ => annularFrequency mode.1 mode.2 ^ grade *
      ‖tupleConjugatedJetSection parameters lower bounded tuple slot order mode‖) :=
  hilbertRadialJetSection_weighted_summable lower bounded (tupleWeightedCurve parameters lower tuple slot)
    (tupleWeightedCurve_smooth parameters lower tuple slot)
    (phaseWeightedCurve_grade (originalPhysicalCoefficient (tuple.val slot))
      (tupleWeightedCurve parameters lower tuple slot) (tupleWeightedCurve_coefficient parameters lower tuple slot)) order grade

/-- Every original split source grade is summable for the actual tuple's
complete radial H1 modes. Only fixed-collar constants are used. -/
theorem tupleConjugatedSourceMode_summable (angular cell : ℕ) :
    Summable (fun mode : ℤ × ℤ => ‖splitTangentialWeight angular cell mode •
      tupleConjugatedRadialGraph parameters lower positive bounded tuple slot mode‖) := by
  have sum := ((tupleConjugatedJet_summable parameters lower bounded tuple slot 0 (angular+cell)).add
    (tupleConjugatedJet_summable parameters lower bounded tuple slot 1 (angular+cell))).mul_left ‖radialSqrtMap 1 lower‖
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ sum
  intro mode
  rw [norm_smul,Real.norm_of_nonneg (splitTangentialWeight_pos angular cell mode).le]
  have bound := mul_le_mul_of_nonneg_left
    (tupleConjugatedRadialGraph_bound parameters lower positive bounded tuple slot mode)
    (splitTangentialWeight_pos angular cell mode).le
  have weight := splitTangentialWeight_le_frequency_pow angular cell mode
  calc
    _ ≤ splitTangentialWeight angular cell mode * (‖radialSqrtMap 1 lower‖ *
      (‖tupleConjugatedJetSection parameters lower bounded tuple slot 0 mode‖ +
        ‖tupleConjugatedJetSection parameters lower bounded tuple slot 1 mode‖)) := bound
    _ ≤ annularFrequency mode.1 mode.2 ^ (angular+cell) * (‖radialSqrtMap 1 lower‖ *
      (‖tupleConjugatedJetSection parameters lower bounded tuple slot 0 mode‖ +
        ‖tupleConjugatedJetSection parameters lower bounded tuple slot 1 mode‖)) :=
      mul_le_mul_of_nonneg_right weight (mul_nonneg (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _)))
    _ = _ := by ring

/-- Actual original H1 source graph of any admissible tuple field, with
literal angular/cell grades and no independently chosen source derivative. -/
def tupleOriginalSourceGraph (angular cell : ℕ) : AnnularSourceH1 parameters 1 lower angular cell :=
  ⟨fun mode => splitTangentialWeight angular cell mode •
    tupleConjugatedRadialGraph parameters lower positive bounded tuple slot mode, by
    have one : Memℓp (fun mode : ℤ × ℤ => splitTangentialWeight angular cell mode •
        tupleConjugatedRadialGraph parameters lower positive bounded tuple slot mode) 1 := by
      apply memℓp_gen
      simpa only [ENNReal.toReal_one,Real.rpow_one] using
        tupleConjugatedSourceMode_summable parameters lower positive bounded tuple slot angular cell
    exact one.of_exponent_ge (by norm_num)⟩

theorem tupleOriginalSourceGraph_stored (angular cell : ℕ) (mode : ℤ × ℤ) (coordinate : Fin 2) :
    weightedRadialCoordinate 1 lower coordinate
      (tupleOriginalSourceGraph parameters lower positive bounded tuple slot angular cell mode) =
      splitTangentialWeight angular cell mode •
        radialSqrtMap 1 lower (tupleConjugatedJetL2 parameters lower positive bounded tuple slot coordinate.val mode) := by
  change weightedRadialCoordinate 1 lower coordinate (splitTangentialWeight angular cell mode • _) = _
  rw [map_smul,tupleConjugatedRadialGraph_coordinate]

theorem tupleOriginalSourceGraph_value (angular cell : ℕ) (mode : ℤ × ℤ) :
    annularConjugatedCoordinate parameters 1 lower positive bounded.le angular cell
      (tupleOriginalSourceGraph parameters lower positive bounded tuple slot angular cell) mode 0 =
      tupleConjugatedJetL2 parameters lower positive bounded tuple slot 0 mode := by
  unfold annularConjugatedCoordinate annularConjugatedMode
  change collarH1Coordinate (ComplexEuclidean 1) lower 0
    ((splitTangentialWeight angular cell mode)⁻¹ • weightedToOrdinary 1 lower positive bounded.le
      (splitTangentialWeight angular cell mode • tupleConjugatedRadialGraph parameters lower positive bounded tuple slot mode)) = _
  simp only [map_smul]
  rw [smul_smul,inv_mul_cancel₀ (splitTangentialWeight_pos angular cell mode).ne',one_smul]
  exact weakRadialRealization_value 1 lower positive bounded _ _ _

theorem tupleOriginalSourceGraph_derivative (angular cell : ℕ) (mode : ℤ × ℤ) :
    annularConjugatedCoordinate parameters 1 lower positive bounded.le angular cell
      (tupleOriginalSourceGraph parameters lower positive bounded tuple slot angular cell) mode 1 =
      tupleConjugatedJetL2 parameters lower positive bounded tuple slot 1 mode := by
  unfold annularConjugatedCoordinate annularConjugatedMode
  change collarH1Coordinate (ComplexEuclidean 1) lower 1
    ((splitTangentialWeight angular cell mode)⁻¹ • weightedToOrdinary 1 lower positive bounded.le
      (splitTangentialWeight angular cell mode • tupleConjugatedRadialGraph parameters lower positive bounded tuple slot mode)) = _
  simp only [map_smul]
  rw [smul_smul,inv_mul_cancel₀ (splitTangentialWeight_pos angular cell mode).ne',one_smul]
  exact weakRadialRealization_slope 1 lower positive bounded _ _ _

end Grad.AnnularOriginalCoreRealization
