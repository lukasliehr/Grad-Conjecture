import AKAV5LiteralG3CollarContinuity

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

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (data : OriginalStrongCarrier parameters lower 0 0)
    (same : data.val.ofLp.1 =
      (actualOriginalSourceDatum parameters length rho epsilon field small lower positive bounded 0 source flat).val.ofLp.1)
    (third : SmoothLowPhysicalRow parameters lower positive
      (strongToLow parameters lower positive bounded.le 0 0
        (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 data)).ofLp.1.ofLp.2)

open Grad.AnnularSmoothCore

include same in
/-- Continuity upgrades the already proved SAME source identity to every radius of the original closed collar. -/
theorem sameThird_fullField_physicalG3_pointwise
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    third.fullField bounded (radius,angles) =
      physicalG3 parameters length epsilon field source radius (positive.le.trans inside.1) inside.2 angles := by
  have agreement := collarCurve_eq_of_ae lower bounded
    (fun current => third.fullField bounded (current,angles))
    (fun current => clampedPhysicalG3 parameters length epsilon field lower positive bounded source (current,angles))
    ((third.fullField_smooth bounded).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn (fun current member => ⟨member,mem_univ _⟩))
    (((clampedPhysicalG3_continuous parameters length rho epsilon field small lower positive bounded source).comp
      (continuous_id.prodMk continuous_const)).continuousOn) ?_
  · exact (agreement inside).trans (clampedPhysicalG3_literal parameters length epsilon field lower positive bounded source radius inside angles)
  · filter_upwards [sameThird_fullField_physicalG3 parameters length rho epsilon field small
      lower positive bounded lengthPositive source flat data same third,ae_restrict_mem measurableSet_Icc] with current actual member
    exact (actual member angles).trans
      (clampedPhysicalG3_literal parameters length epsilon field lower positive bounded source current member angles).symm

include same in
/-- Pointwise exact original source fidelity for the SAME third field used in the physical radial equation. -/
theorem sameThird_fullField_literalG3_pointwise
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    third.fullField bounded (radius,angles) 0 =
      (actualAnnularBulkSource parameters length epsilon field radius
        (by rw [abs_of_nonneg (positive.le.trans inside.1)]; exact inside.2)
        angles.2 (spinToCartesian source)).G3 angles.1 := by
  exact (congrArg (fun value : ComplexEuclidean 1 => value 0)
    (sameThird_fullField_physicalG3_pointwise parameters length rho epsilon field small
      lower positive bounded lengthPositive source flat data same third radius inside angles)).trans
    (physicalG3_literal parameters length rho epsilon field small source radius
      (positive.le.trans inside.1) inside.2 angles.1 angles.2)

end Grad.ActualOriginalThirdSource
