import AKAT22SameSevenKnownSources

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.ActualCartesianEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.SourceCollarFullSource Grad.SourceCollarBulk Grad.SourceCollarRestriction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarFlux Grad.BoundaryTrace Grad.SourceCollar
open Grad.AnnularGeneralSourceRegularity Grad.AnnularCurrentLow Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularStrongOrbit Grad.AnnularSourceGraph Grad.AnnularForwardDatum Grad.AnnularRestriction
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.Allocation Grad.BoundaryLift Grad.ActualOriginalThirdSource
open Grad.AnnularOriginalSmoothCore

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (source : SmoothQuotient parameters) (flat : IsFlat source)

    (data : OriginalStrongCarrier parameters lower 0 0)
    (same : data.val.ofLp.1 =
      (actualOriginalSourceDatum parameters length rho epsilon field small lower positive bounded 0 source flat).val.ofLp.1)

/-- Reuse the existing actual source curves, preserving arbitrary incoming data. -/
def sameKnownSourceCurves (slot : Fin 4) :
    SmoothLowPhysicalRow parameters lower positive
      (strongKnownBulk parameters lower positive bounded.le
        (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 data) slot) where
  curve := actualCartesianPrimitiveCurve parameters length lower positive bounded source slot
  smooth grade := (actualCartesianPrimitiveRadialCurves parameters length lower positive bounded source slot).smooth grade
  same grade := by
    rw [originalKnownBulk_same_sources parameters lower length positive bounded lengthPositive _ data same]
    exact actualCartesianPrimitiveCurve_actual parameters length rho epsilon field small lower positive bounded lengthPositive source flat slot grade

include same in
/-- F0 and F2 inside the SAME seven packet are the literal original source
values, with the original L^-1 normalization of F2. -/
theorem sameSevenKnown_literal
    (solution : Grad.AnnularCoupledInverse.CoupledSpace lower length positive lengthPositive)
    (seven : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le
        (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 data) solution))
    (component : Fin 2) (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (seven.bulkUnit (0 : Fin 1) (![4,6] component)).fullField bounded (radius,angles) =
      literalPrimitiveSource parameters length source radius (positive.le.trans inside.1) inside.2 (![1,2] component) angles := by
  let sourceCurves := sameKnownSourceCurves parameters length rho epsilon field small lower positive bounded lengthPositive source flat data same
  fin_cases component
  · have actual := sameSevenKnown_fullField parameters lower length positive bounded lengthPositive
      (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 data) solution seven 0 (sourceCurves 0) radius inside angles
    exact actual.trans (sameKnownSource_fullField_literal parameters length rho epsilon field small lower positive bounded lengthPositive
      source flat data same 1 (sourceCurves 0) radius inside angles)
  · have actual := sameSevenKnown_fullField parameters lower length positive bounded lengthPositive
      (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 data) solution seven 2 (sourceCurves 2) radius inside angles
    exact actual.trans (sameKnownSource_fullField_literal parameters length rho epsilon field small lower positive bounded lengthPositive
      source flat data same 2 (sourceCurves 2) radius inside angles)

end Grad.ActualCartesianEquations
