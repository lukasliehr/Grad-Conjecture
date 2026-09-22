import AKN28ActualOriginalSourceDatum

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Grad.ExhaustionSourceAllocation
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.SourceCollarFullSource Grad.SourceCollarCoefficients Grad.SourceBoundaryTrace Grad.AnnularCurrentSource
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection Grad.Constraints Grad.BoundaryTrace
open Grad.SourceCollarBulk Grad.AnnularStrongData Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularExhaustionEstimate
attribute [local instance] Grad.AnnularStrongOrbit.knownAmbientNormed Grad.AnnularStrongOrbit.knownAmbientSeminormed Grad.AnnularStrongOrbit.knownAmbientRealNormed Grad.AnnularStrongOrbit.knownAmbientRealModule
  Grad.AnnularStrongOrbit.strongCarrierNormed Grad.AnnularStrongOrbit.strongCarrierSeminormed Grad.AnnularStrongOrbit.strongCarrierRealNormed Grad.AnnularStrongOrbit.strongCarrierRealModule

/-- The exact weighted original datum norm is controlled by the six actual
BF rows and the two genuine AH graphs; no boundary comparison enters. -/
theorem actualOriginalSourceDatum_weighted_norm_sum (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (lengthPositive : 0 < L) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ)
    (source : SmoothQuotient parameters) (flat : IsFlat source) :
    originalWeightedDatumNorm parameters lower L positive bounded.le lengthPositive
      (actualOriginalSourceDatum parameters L rho epsilon field small lower positive bounded grade source flat) ≤
    ‖divisionHighWeight lower positive bounded.le (unweightedSourceF0Bulk parameters lower
      (actualOriginalF0Graph parameters lower positive bounded grade source))‖ +
    ‖divisionHighWeight lower positive bounded.le (unweightedSourceRF0Bulk parameters lower
      (actualOriginalF0Graph parameters lower positive bounded grade source))‖ +
    ‖divisionHighWeight lower positive bounded.le (unweightedSourceF2Bulk parameters lower
      (actualOriginalF2Graph parameters L lower positive bounded grade source))‖ +
    ‖divisionHighWeight lower positive bounded.le (actualOriginalF1Row parameters lower positive bounded.le grade source)‖ +
    ‖divisionHighWeight lower positive bounded.le (originalAngularDecode lower
      (actualOriginalG3Row parameters L rho epsilon field small lower positive bounded.le grade source))‖ +
    ‖divisionHighWeight lower positive bounded.le (sourceAngularBulk lower
      (actualOriginalG3Row parameters L rho epsilon field small lower positive bounded.le grade source))‖ +
    ‖actualOriginalF0Graph parameters lower positive bounded grade source‖ +
    ‖actualOriginalF2Graph parameters L lower positive bounded grade source‖ := by
  unfold originalWeightedDatumNorm
  rw [originalWeightedDatum_explicit]
  have bound := StrongDataCarrier.norm_le_sum parameters lower positive bounded.le 0 0
    (originalToStrong parameters lower L positive bounded.le lengthPositive 0 0
      (actualOriginalSourceDatum parameters L rho epsilon field small lower positive bounded grade source flat))
  change _ ≤
    ‖divisionHighWeight lower positive bounded.le (unweightedSourceF0Bulk parameters lower
      (actualOriginalF0Graph parameters lower positive bounded grade source))‖ +
    ‖divisionHighWeight lower positive bounded.le (unweightedSourceRF0Bulk parameters lower
      (actualOriginalF0Graph parameters lower positive bounded grade source))‖ +
    ‖divisionHighWeight lower positive bounded.le (unweightedSourceF2Bulk parameters lower
      (actualOriginalF2Graph parameters L lower positive bounded grade source))‖ +
    ‖divisionHighWeight lower positive bounded.le (actualOriginalF1Row parameters lower positive bounded.le grade source)‖ +
    ‖divisionHighWeight lower positive bounded.le (originalAngularDecode lower
      (actualOriginalG3Row parameters L rho epsilon field small lower positive bounded.le grade source))‖ +
    ‖divisionHighWeight lower positive bounded.le (sourceAngularBulk lower
      (actualOriginalG3Row parameters L rho epsilon field small lower positive bounded.le grade source))‖ +
    ‖actualOriginalF0Graph parameters lower positive bounded grade source‖ +
    ‖actualOriginalF2Graph parameters L lower positive bounded grade source‖ +
    ‖(0 : Grad.ActualBoundaryPrimitives.HighBoundaryPrimitive parameters 0 0)‖ +
    ‖lower ^ (-9 / 4 : ℝ) • (0 : Grad.AnnularVariational.AnnularBoundary)‖ +
    ‖originalLowIncomingWeightMap parameters lower L positive bounded.le lengthPositive 0‖ at bound
  simpa only [smul_zero, map_zero, norm_zero, add_zero] using bound

/-- Uniform moving-collar source allocation before the harmless final grade
monotonicity: strongest source grade t+6, state grade t+6, and fixed source5. -/
theorem actualOriginalSourceDatum_weighted_bound (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (lengthPositive : 0 < L) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ)
    (source : SmoothQuotient parameters) (flat : IsFlat source) (vanishing : SourceHigherVanishing source) :
    originalWeightedDatumNorm parameters lower L positive bounded.le lengthPositive
      (actualOriginalSourceDatum parameters L rho epsilon field small lower positive bounded grade source flat) ≤
      3 * tiltedForceConstant (grade + 1) * ‖quotientEta parameters (grade + 6) source‖ +
      (|L⁻¹| * Real.sqrt (remainderAngularBoundConstant 3 grade 0)) * ‖quotientEta parameters (grade + 5) source‖ +
      (planarBulkConstant grade + L⁻¹ * restrictionGraphConstant grade 1) * ‖quotientEta parameters (grade + 2) source‖ +
      2 * (tiltedG3HighConstant parameters L (grade + 1) * ‖quotientEta parameters (grade + 6) source‖ +
        3 * tiltedCoefficientLowConstant parameters L (grade + 1) * physicalBudget parameters field rho epsilon (grade + 6) *
          ‖quotientEta parameters 5 source‖) := by
  have total := actualOriginalSourceDatum_weighted_norm_sum parameters L rho epsilon lengthPositive field small
    lower positive bounded grade source flat
  have f0 := actualOriginalF0Bulk_tilted_bound parameters source vanishing lower positive bounded grade
  have rf0 := actualOriginalRF0Bulk_tilted_bound parameters source vanishing lower positive bounded grade
  have f2 := actualOriginalF2Graph_tilted_coordinate_bound parameters L source vanishing lower positive bounded grade
  have f1 := actualOriginalF1Row_tilted_bound parameters source vanishing lower positive bounded.le grade
  have fullG3 := actualOriginalG3Row_tilted_pair_bound parameters L rho epsilon field small source vanishing lower positive bounded.le grade
  have graph0 := actualOriginalF0Graph_bound parameters lower positive bounded grade source
  have graph2 := actualOriginalF2Graph_bound parameters L lower lengthPositive positive bounded grade source
  change ‖divisionHighWeight lower positive bounded.le (unweightedSourceF2Bulk parameters lower
      (actualOriginalF2Graph parameters L lower positive bounded grade source))‖ ≤ _ at f2
  dsimp only at fullG3
  linarith only [total, f0, rf0, f2, f1, fullG3.1, fullG3.2, graph0, graph2]

end Grad.ExhaustionSourceAllocation
