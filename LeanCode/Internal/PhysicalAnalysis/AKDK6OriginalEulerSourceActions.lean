import AKDK5ActualSourceEulerEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped ENNReal
namespace Grad.OriginalTerminalAllocation
open Grad.OriginalCartesianTameEstimate Grad.CartesianState Grad.AnnularGeneralSourceRegularity
open Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.NonlinearProduct

section Linear
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F]

theorem rawEulerPolynomial_map (action : E →L[ℂ] F) (jets : ℕ → ℝ → E) (terms : List (ℕ × ℝ)) (radius : ℝ) :
    rawEulerPolynomial (fun raw point => action (jets raw point)) terms radius =
      action (rawEulerPolynomial jets terms radius) := by
  induction terms with
  | nil => exact (map_zero action).symm
  | cons term terms previous =>
      change term.2 • (radius^(term.1+1) • action (jets (term.1+1) radius))+
        rawEulerPolynomial (fun raw point => action (jets raw point)) terms radius = _
      rw [previous]
      change term.2 • (radius^(term.1+1) • action (jets (term.1+1) radius))+action (rawEulerPolynomial jets terms radius) =
        action (term.2 • (radius^(term.1+1) • jets (term.1+1) radius)+rawEulerPolynomial jets terms radius)
      rw [map_add]
      congr 1
      exact ((action.restrictScalars ℝ).map_smul term.2 (radius^(term.1+1) • jets (term.1+1) radius)).trans
        (congrArg (term.2 • ·) ((action.restrictScalars ℝ).map_smul (radius^(term.1+1)) (jets (term.1+1) radius))) |>.symm

theorem actualRawEulerJets_map (action : E →L[ℂ] F) (jets : ℕ → ℝ → E) (rank : ℕ) (radius : ℝ) :
    actualRawEulerJets (fun raw point => action (jets raw point)) rank radius =
      action (actualRawEulerJets jets rank radius) := by
  cases rank with
  | zero => rfl
  | succ rank => exact rawEulerPolynomial_map action jets (positiveEulerTerms rank) radius

end Linear

/-- Fixed angular/radial Hilbert contractions commute with every genuine
Euler derivative of the same weighted source and preserve its payment. -/
theorem actualCartesianAction_eulerEnergy {input output grade power rank : ℕ}
    (parameters : PhaseParameters) (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (paid : power+rank≤grade) (field : ACore parameters input)
    (action : CellL2 input →L[ℂ] CellL2 output) :
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank
        (fun point => action (cartesianWeightedRadialCurve parameters lower positive bounded field power 0 point)) radius‖^2)) ≤
      ENNReal.ofReal ((‖action‖*(originalEulerCurveConstant lower power rank*originalGradeNorm grade field))^2) := by
  let jets := cartesianWeightedRadialCurve parameters lower positive bounded field power
  have nonzero : ∀ radius ∈ Icc lower 1, radius≠0 := fun radius inside => (positive.trans_le inside.1).ne'
  have original := actualRawEulerJets_fidelity (Icc lower 1) (uniqueDiffOn_Icc bounded) nonzero jets
    (fun raw radius inside => cartesianWeightedRadialCurve_derivative parameters lower positive bounded field power raw radius inside) rank
  have mapped := actualRawEulerJets_fidelity (Icc lower 1) (uniqueDiffOn_Icc bounded) nonzero
    (fun raw point => action (jets raw point)) (fun raw radius inside =>
      (action.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt radius
        (cartesianWeightedRadialCurve_derivative parameters lower positive bounded field power raw radius inside)) rank
  have same : (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank (fun point => action (jets 0 point)) radius‖^2)) =
      (∫⁻ radius in Icc lower 1, ENNReal.ofReal
        (‖action (vectorEulerWithinIteratedDerivative (Icc lower 1) rank (jets 0) radius)‖^2)) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
    rw [mapped inside,actualRawEulerJets_map,← original inside]
  rw [same]
  exact boundedAction_squareEnergy lower action _ _ (actualCartesianCurve_eulerCollarEnergy parameters lower positive bounded paid field)

end Grad.OriginalTerminalAllocation
