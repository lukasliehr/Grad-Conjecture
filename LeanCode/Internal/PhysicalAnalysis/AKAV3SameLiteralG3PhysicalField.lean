import AKAV2SameThirdOriginalCoefficients

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

include same in
/-- The SAME actual reconstructed third-source field equals full physical G3 for almost every radius and all angles. -/
theorem sameThird_fullField_physicalG3 :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ angles : ℝ × ℝ,
      third.fullField bounded (radius,angles) =
        physicalG3 parameters length epsilon field source radius (positive.le.trans inside.1) inside.2 angles := by
  filter_upwards [sameSourceThird_physicalCoefficients parameters length rho epsilon field small
      lower positive bounded lengthPositive source flat data same,
    third.physicalCurve_actual bounded 0] with radius original represented
  intro inside angles
  have periodic := physicalG3_periodic parameters length rho epsilon field small source radius (positive.le.trans inside.1) inside.2
  apply congrFun (third.fullField_eq_of_doubleCoefficient bounded radius inside
    (physicalG3 parameters length epsilon field source radius (positive.le.trans inside.1) inside.2)
    (physicalG3_continuous parameters length rho epsilon field small source radius (positive.le.trans inside.1) inside.2)
    periodic.1 periodic.2 ?_) angles
  intro mode
  exact (original inside mode).symm.trans (by simpa only [pow_zero,one_smul] using (represented mode).symm)

include same in
/-- The original G/L and P((kappa1 F1+kappa2 F0-kappa3 F2)/r), including the circular correction, are exactly the SAME actual third source. -/
theorem sameThird_fullField_literalG3 :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ angles : ℝ × ℝ,
      third.fullField bounded (radius,angles) 0 =
        (actualAnnularBulkSource parameters length epsilon field radius
          (by rw [abs_of_nonneg (positive.le.trans inside.1)]; exact inside.2)
          angles.2 (spinToCartesian source)).G3 angles.1 := by
  filter_upwards [sameThird_fullField_physicalG3 parameters length rho epsilon field small
    lower positive bounded lengthPositive source flat data same third] with radius actual
  intro inside angles
  rw [actual inside angles]
  exact physicalG3_literal parameters length rho epsilon field small source radius
    (positive.le.trans inside.1) inside.2 angles.1 angles.2

end Grad.ActualOriginalThirdSource
