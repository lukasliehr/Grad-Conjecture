import AIW17BoundedOriginalLowGradeInclusions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularOriginalLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.PhaseAlgebra Grad.CircularHighRegularity
open Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Literal AJ8 Hilbert norm: v and Lambda^-1 v' in dr. -/
theorem originalLowGraph_literal_norm_sq (lower : ℝ) (bounded : lower ≤ 1) (field : originalLowGraph lower) :
    ‖field‖ ^ 2 =
      (∑' index : LowAnnularIndex, ∫ radius in lower..1, ‖field.val 0 index radius‖ ^ 2) +
      (∑' index : LowAnnularIndex, ∫ radius in lower..1, ‖field.val 1 index radius‖ ^ 2) := by
  rw [originalLowGraph_norm_sq]
  have first := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (field.val 0)
  have second := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (field.val 1)
  norm_num at first second
  rw [first, second]
  have coordinate (slot : Fin 2) (index : LowAnnularIndex) :
      ‖field.val slot index‖ ^ 2 = ∫ radius in lower..1, ‖field.val slot index radius‖ ^ 2 := by
    rw [radialLp_norm_sq, intervalIntegral.integral_of_le bounded, ← integral_Icc_eq_integral_Ioc]
  congr 1
  · exact tsum_congr (coordinate 0)
  · exact tsum_congr (coordinate 1)

/-- The physical representative in AIW7 is the actual image of the inverse,
not merely an unrelated pointwise coordinate construction. -/
theorem originalLowBF6_section_bulk (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    radialSectionL2 1 lower positive bounded.le
      (originalLowAJSection parameters lower length positive bounded field index) =
      ((originalLowGraphEquivalence parameters lower length positive lengthPositive bounded.le).symm field).val 0 index := by
  rw [originalLowAJSection, radialSectionL2_scalar, lowEnergySection_bulk]
  exact (originalLowToAJAmbient_value parameters lower length positive lengthPositive bounded.le field index).symm

/-- Geometry constants are chosen before every positive collar. The original
AJ6 gamma>0 guard is carried by PhaseParameters, and no extra low tilt appears. -/
theorem originalLowBF6_uniform (parameters : PhaseParameters) (length : ℝ) (lengthPositive : 0 < length) :
    ∃ inverseConstant > 0, ∃ forwardConstant > 0, ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1),
      (∀ field : originalLowGraph lower,
        ‖originalLowGraphEquivalence parameters lower length positive lengthPositive bounded field‖ ≤
          forwardConstant * lower ^ (-(15 / 4 : ℝ)) * ‖field‖) ∧
      (∀ field : lowEnergyGraph lower length positive,
        ‖(originalLowGraphEquivalence parameters lower length positive lengthPositive bounded).symm field‖ ≤
          inverseConstant * lower⁻¹ * ‖field‖) := by
  refine ⟨3 * originalLowToAJConstant parameters length, ?_,
    3 * originalLowFromAJConstant parameters length, ?_, ?_⟩
  · have one := (originalLowToAJConstant_dominates parameters length lengthPositive).2.2.2
    linarith
  · have one := (originalLowFromAJConstant_dominates parameters length lengthPositive).2.2.2
    linarith
  · intro lower positive bounded
    exact ⟨originalLowGraphEquivalence_bound parameters lower length positive lengthPositive bounded,
      originalLowGraphEquivalence_inverse_bound parameters lower length positive lengthPositive bounded⟩

theorem originalLowBF6_exact_solution (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1)
    (field : lowEnergyGraph lower length positive) :
    ∃! original : originalLowGraph lower,
      originalLowGraphEquivalence parameters lower length positive lengthPositive bounded original = field := by
  let equivalence := originalLowGraphEquivalence parameters lower length positive lengthPositive bounded
  refine ⟨equivalence.symm field, equivalence.apply_symm_apply field, ?_⟩
  intro original same
  exact equivalence.injective (same.trans (equivalence.apply_symm_apply field).symm)

/-- Every original AJ Sobolev inclusion commutes with the SAME inverse. -/
theorem originalLowBF6_inverse_inclusion (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1)
    (grade larger : ℕ) (included : grade ≤ larger) (field : lowEnergyGraph lower length positive) :
    (originalLowGraphEquivalence parameters lower length positive lengthPositive bounded).symm
      (originalLowYInclusion lower length positive grade larger included field) =
    originalLowAJInclusion lower grade larger included
      ((originalLowGraphEquivalence parameters lower length positive lengthPositive bounded).symm field) :=
  originalLowUnweight_diagonal lower (originalLowCellGradeRatio grade larger) 1 (by norm_num)
    (originalLowCellGradeRatio_bound grade larger included) parameters length positive lengthPositive bounded field

end Grad.AnnularOriginalLow
