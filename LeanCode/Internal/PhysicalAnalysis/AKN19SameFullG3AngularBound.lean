import AKN18FullTiltedG3

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Grad.ExhaustionSourceAllocation

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarFullSource
open Grad.SourceCollarBulk Grad.SourceCollarCoefficients Grad.AnnularCurrentSource
open Grad.GaugeCoefficients.Physical.Allocation Grad.AxisCore Grad.QuotientProjection

theorem divisionHighWeight_lowering (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : DivisionRow 1 lower) :
    divisionHighWeight lower positive bounded (annularWeightLoweringRowValue lower field) =
      annularWeightLoweringRowValue lower (divisionHighWeight lower positive bounded field) := by
  apply lp.ext
  funext mode
  rw [divisionHighWeight_mode]
  change _ = annularWeightLoweringRatio mode • divisionHighWeight lower positive bounded field mode
  rw [divisionHighWeight_mode]
  exact map_smul _ _ _

theorem divisionHighWeight_angular (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : DivisionRow 1 lower) :
    divisionHighWeight lower positive bounded (annularAngularRow lower field) =
      annularAngularRow lower (divisionHighWeight lower positive bounded field) := by
  apply lp.ext
  funext mode
  rw [divisionHighWeight_mode]
  change _ = annularAngularRatio mode • divisionHighWeight lower positive bounded field mode
  rw [divisionHighWeight_mode]
  exact map_smul _ _ _

/-- Both actual G3 and actual RG3 inherit one uniform bound from the same
strong G3 row. The original strengthened g is retained. -/
theorem actualG3_pair_tilted_bound {grade order : ℕ}
    (parameters : PhaseParameters) (L rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (source : SmoothQuotient parameters) (flat : SourceHigherVanishing source) (paid : order + 6 ≤ grade)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) :
    let estimate := tiltedG3HighConstant parameters L (order + 1) * ‖quotientEta parameters grade source‖ +
      3 * tiltedCoefficientLowConstant parameters L (order + 1) * physicalBudget parameters field rho epsilon (order + 6) *
        ‖quotientEta parameters 5 source‖
    ‖divisionHighWeight lower positive bounded
      (g3ValueRow (order := order) parameters L rho epsilon field small lower positive bounded (by omega)
        (quotientEta parameters grade source))‖ ≤ estimate ∧
    ‖divisionHighWeight lower positive bounded
      (g3AngularRow (order := order) parameters L rho epsilon field small lower positive bounded (by omega)
        (quotientEta parameters grade source))‖ ≤ estimate := by
  have bound := actualFullG3_tilted_bound (power := order + 1) parameters L rho epsilon field small source flat
    (by omega : order + 1 + 5 ≤ grade) lower positive bounded
  constructor
  · rw [g3ValueRow, divisionHighWeight_lowering]
    exact (annularWeightLoweringRowValue_norm_le lower _).trans bound
  · rw [g3AngularRow, divisionHighWeight_angular]
    exact (annularAngularRowValue_norm_le lower _).trans bound

end Grad.ExhaustionSourceAllocation
