import AKAV1LiteralOriginalG3Periodic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualOriginalThirdSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.SourceCollarFullSource Grad.SourceCollarBulk Grad.SourceCollarRestriction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarFlux Grad.BoundaryTrace Grad.SourceCollar
open Grad.AnnularGeneralSourceRegularity Grad.AnnularCurrentLow Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularStrongOrbit Grad.AnnularSourceGraph Grad.AnnularForwardDatum Grad.AnnularRestriction
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.Allocation Grad.BoundaryLift

open Grad.AnnularOriginalSmoothCore

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (source : SmoothQuotient parameters) (flat : IsFlat source)

/-- Exact phase/rho decoding of the full prescribed G3 source, with every correction retained. -/
theorem actualCartesianThird_physicalCoefficients :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ mode : ℤ × ℤ,
      lowRhoPhysicalCoefficient parameters lower positive
        (strongToLow parameters lower positive bounded.le 0 0
          (actualCartesianWeightedDatum parameters length rho epsilon field small lower positive bounded lengthPositive source flat)).ofLp.1.ofLp.2 radius mode =
      doubleCoefficient (physicalG3 parameters length epsilon field source radius (positive.le.trans inside.1) inside.2) mode := by
  rw [actualCartesianThirdRow_stored parameters length rho epsilon field small lower positive bounded lengthPositive source flat]
  change ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ mode : ℤ × ℤ,
    originalF1Coefficient parameters lower positive bounded.le
      (originalAngularDecode lower (actualOriginalG3Row parameters length rho epsilon field small lower positive bounded.le 0 source)) radius mode = _
  filter_upwards [originalF1Coefficient_eq_originalRow parameters lower positive bounded
      (originalAngularDecode lower (actualOriginalG3Row parameters length rho epsilon field small lower positive bounded.le 0 source)),
    actualG3Value_same_physical parameters length rho epsilon field small lower positive bounded.le 0 source flat]
      with radius decoded actual
  intro inside mode
  rw [decoded mode,(actualOriginalG3Row_decode parameters length rho epsilon field small lower positive bounded.le 0 source).1]
  exact actual inside mode

/-- Changing only incoming/boundary data preserves the literal original third source. -/
theorem sameSourceThird_physicalCoefficients
    (data : OriginalStrongCarrier parameters lower 0 0)
    (same : data.val.ofLp.1 =
      (actualOriginalSourceDatum parameters length rho epsilon field small lower positive bounded 0 source flat).val.ofLp.1) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ mode : ℤ × ℤ,
      lowRhoPhysicalCoefficient parameters lower positive
        (strongToLow parameters lower positive bounded.le 0 0
          (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 data)).ofLp.1.ofLp.2 radius mode =
      doubleCoefficient (physicalG3 parameters length epsilon field source radius (positive.le.trans inside.1) inside.2) mode := by
  rw [originalThirdBulk_same_sources parameters lower length positive bounded lengthPositive _ data same]
  exact actualCartesianThird_physicalCoefficients parameters length rho epsilon field small lower positive bounded lengthPositive source flat

end Grad.ActualOriginalThirdSource
