import AKN21OriginalSourceGraphRealization
import SRC9BS36Consumer

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Grad.ExhaustionSourceAllocation
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularSourceGraph
open Grad.SourceCollarBulk Grad.SourceCollarRestriction Grad.AxisCore Grad.QuotientProjection

def derivativeGraphRealization (parameters : PhaseParameters) (dimension : ℕ)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (field : annularDerivativeGraph dimension lower positive 1) :
    AnnularSourceH1 parameters dimension lower angular cell :=
  sourceGraphRealization parameters dimension lower positive bounded angular cell (field.val 0) (field.val 1)
    (fun mode => (annularDerivativeGraph_mem_iff lower positive 1 field.val).mp field.property 0 mode)

theorem derivativeGraphRealization_coordinate (parameters : PhaseParameters) (dimension : ℕ)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (field : annularDerivativeGraph dimension lower positive 1) (coordinate : Fin 2) :
    annularSourceCoordinate parameters dimension lower angular cell coordinate
      (derivativeGraphRealization parameters dimension lower positive bounded angular cell field) = field.val coordinate := by
  fin_cases coordinate
  · exact sourceGraphRealization_value parameters dimension lower positive bounded angular cell _ _ _
  · exact sourceGraphRealization_derivative parameters dimension lower positive bounded angular cell _ _ _

theorem derivativeGraphRealization_bound (parameters : PhaseParameters) (dimension : ℕ)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (field : annularDerivativeGraph dimension lower positive 1) :
    ‖derivativeGraphRealization parameters dimension lower positive bounded angular cell field‖ ≤ ‖field‖ := by
  have bound := sourceGraphRealization_bound parameters dimension lower positive bounded angular cell
    (field.val 0) (field.val 1)
    (fun mode => (annularDerivativeGraph_mem_iff lower positive 1 field.val).mp field.property 0 mode)
  change _ ≤ ‖field.val‖
  rw [PiLp.norm_eq_of_L1, Fin.sum_univ_two]
  exact bound

/-- SAME original F0 source graph: the exact AH multiplier
nu^grade(1+|m|), on its value and genuine weighted radial derivative. -/
def actualOriginalF0Graph (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ)
    (source : SmoothQuotient parameters) : AnnularSourceH1 parameters 1 lower 1 0 :=
  derivativeGraphRealization parameters 1 lower positive bounded 1 0
    (completedForceS11 lower positive bounded.le parameters grade (quotientEta parameters (grade + 2) source))

/-- SAME original F2=h/L source graph, including its genuine weighted radial derivative. -/
def actualOriginalF2Graph (parameters : PhaseParameters) (L lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ)
    (source : SmoothQuotient parameters) : AnnularSourceH1 parameters 1 lower 0 0 :=
  derivativeGraphRealization parameters 1 lower positive bounded 0 0
    (completedFourthSource lower positive bounded.le parameters L grade (quotientEta parameters (grade + 2) source))

theorem actualOriginalF0Graph_coordinate (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ)
    (source : SmoothQuotient parameters) (coordinate : Fin 2) :
    annularSourceCoordinate parameters 1 lower 1 0 coordinate
      (actualOriginalF0Graph parameters lower positive bounded grade source) =
      (completedForceS11 lower positive bounded.le parameters grade (quotientEta parameters (grade + 2) source)).val coordinate :=
  derivativeGraphRealization_coordinate parameters 1 lower positive bounded 1 0 _ coordinate

theorem actualOriginalF2Graph_coordinate (parameters : PhaseParameters) (L lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ)
    (source : SmoothQuotient parameters) (coordinate : Fin 2) :
    annularSourceCoordinate parameters 1 lower 0 0 coordinate
      (actualOriginalF2Graph parameters L lower positive bounded grade source) =
      (completedFourthSource lower positive bounded.le parameters L grade (quotientEta parameters (grade + 2) source)).val coordinate :=
  derivativeGraphRealization_coordinate parameters 1 lower positive bounded 0 0 _ coordinate

theorem actualOriginalF0Graph_bound (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ)
    (source : SmoothQuotient parameters) :
    ‖actualOriginalF0Graph parameters lower positive bounded grade source‖ ≤
      planarBulkConstant grade * ‖quotientEta parameters (grade + 2) source‖ :=
  (derivativeGraphRealization_bound parameters 1 lower positive bounded 1 0 _).trans
    (completedForceS11_bound lower positive bounded.le parameters grade _)

theorem actualOriginalF2Graph_bound (parameters : PhaseParameters) (L lower : ℝ)
    (lengthPositive : 0 < L) (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ)
    (source : SmoothQuotient parameters) :
    ‖actualOriginalF2Graph parameters L lower positive bounded grade source‖ ≤
      (L⁻¹ * restrictionGraphConstant grade 1) * ‖quotientEta parameters (grade + 2) source‖ :=
  (derivativeGraphRealization_bound parameters 1 lower positive bounded 0 0 _).trans
    (completedFourthSource_bound lower positive bounded.le parameters L lengthPositive grade _)

end Grad.ExhaustionSourceAllocation
