import AKAT17ActualOriginalThirdEquation
import AKAV6SameLiteralG3PointwiseConsumer

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

/-- The literal original Cartesian source coefficients survive both stored radial weights exactly. -/
theorem originalCartesianRow_physicalCoefficients {dimension : ℕ}
    (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : ACore parameters dimension) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ mode : ℤ × ℤ,
      originalRowCoefficient parameters 0 lower (cartesianWeightedRadialRow parameters lower positive bounded field 0 0) radius mode =
        angularCoefficient (fun angle => (field.val mode.2).value
          (polarClosedPoint radius angle (positive.le.trans inside.1) inside.2)) mode.1 := by
  filter_upwards [ae_all_iff.mpr (fun mode : ℤ × ℤ => restrictionModeLp_weighted_core_ae lower positive parameters 0 0 field mode)]
    with radius stored
  intro inside mode
  change (originalRowWeight parameters 0 radius mode : ℂ)⁻¹ • restrictionModeLp lower 0 0 parameters field mode radius = _
  rw [stored mode]
  change _ • ((annularFrequency mode.1 mode.2 : ℂ)^0 • (Real.sqrt radius •
    angularCoefficient (fun angle => originalPolarValue (phaseWeightedJet parameters mode.2 (field.val mode.2)) (radius,angle)) mode.1)) = _
  simp_rw [originalPolarValue_closed _ radius _ (positive.le.trans inside.1) inside.2,phaseWeightedJet_value]
  exact decode_weighted_angular parameters 0 radius (positive.trans_le inside.1) mode _

/-- The physical source uses the same two Fourier circles and the original unweighted Cartesian value. -/
theorem corePolarValue_doubleCoefficient {dimension : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (mode : ℤ × ℤ) :
    doubleCoefficient (corePolarValue parameters field radius nonnegative bounded) mode =
      angularCoefficient (fun angle => (field.val mode.2).value
        (polarClosedPoint radius angle nonnegative bounded)) mode.1 := by
  unfold doubleCoefficient
  simp_rw [corePolarValue_axialCoefficient]

end Grad.ActualCartesianEquations
