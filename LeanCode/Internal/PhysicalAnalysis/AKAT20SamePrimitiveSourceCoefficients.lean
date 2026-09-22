import AKAT19LiteralPrimitiveSourceCoefficients

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

/-- Exact SAME prescribed F1/F0/F2, after the original source datum and both stored weights. -/
theorem actualKnownSource_physicalCoefficients (component : Fin 3) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ mode : ℤ × ℤ,
      lowRhoPhysicalCoefficient parameters lower positive
        (strongKnownBulk parameters lower positive bounded.le
          (actualCartesianWeightedDatum parameters length rho epsilon field small lower positive bounded lengthPositive source flat)
            (primitiveKnownSlot component)) radius mode =
        doubleCoefficient (literalPrimitiveSource parameters length source radius (positive.le.trans inside.1) inside.2 component) mode := by
  rw [actualCartesianKnownRow_stored parameters length rho epsilon field small lower positive bounded lengthPositive source flat]
  change ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ mode : ℤ × ℤ,
    originalF1Coefficient parameters lower positive bounded.le
      (actualCartesianPrimitiveRows parameters length lower positive bounded source (primitiveKnownSlot component)) radius mode = _
  filter_upwards [originalF1Coefficient_eq_originalRow parameters lower positive bounded
      (actualCartesianPrimitiveRows parameters length lower positive bounded source (primitiveKnownSlot component)),
    actualPrimitiveSources_originalCoefficients parameters length lower positive bounded source] with radius decoded actual
  intro inside mode
  rw [decoded mode]
  exact actual inside component mode

/-- Original incoming data are arbitrary; exact original source-block equality is sufficient. -/
theorem sameKnownSource_physicalCoefficients
    (data : OriginalStrongCarrier parameters lower 0 0)
    (same : data.val.ofLp.1 =
      (actualOriginalSourceDatum parameters length rho epsilon field small lower positive bounded 0 source flat).val.ofLp.1)
    (component : Fin 3) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ mode : ℤ × ℤ,
      lowRhoPhysicalCoefficient parameters lower positive
        (strongKnownBulk parameters lower positive bounded.le
          (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 data)
            (primitiveKnownSlot component)) radius mode =
        doubleCoefficient (literalPrimitiveSource parameters length source radius (positive.le.trans inside.1) inside.2 component) mode := by
  rw [originalKnownBulk_same_sources parameters lower length positive bounded lengthPositive _ data same]
  exact actualKnownSource_physicalCoefficients parameters length rho epsilon field small lower positive bounded lengthPositive source flat component

end Grad.ActualCartesianEquations
