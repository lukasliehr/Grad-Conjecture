import AKG8FullOuterBoundaryPreservation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open Set MeasureTheory Filter
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularFluxTrace Grad.AnnularOmegaGraph
open Grad.AnnularCurrentSource Grad.AnnularCrossMaps Grad.AnnularLowEnergy Grad.AnnularCurrentLow
open Grad.AnnularStrongSolution Grad.AnnularSmoothCore Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.GaugeCoefficients.Physical.Ledger

/-- The original common storage factor depends on the actual radius,
not on the auxiliary lower-endpoint extension. -/
theorem restrictionLowRhoWeight (parameters : PhaseParameters) (lower upper : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (included : lower ≤ upper)
    (radius : ℝ) (inside : radius ∈ Icc upper 1) (mode : ℤ × ℤ) :
    lowRhoPhysicalWeight parameters upper upperPositive radius mode =
      lowRhoPhysicalWeight parameters lower lowerPositive radius mode := by
  change (max upper radius) ^ (-(7 / 4 : ℝ)) * Real.exp _ =
    (max lower radius) ^ (-(7 / 4 : ℝ)) * Real.exp _
  rw [max_eq_right inside.1,max_eq_right (included.trans inside.1)]

/-- Exact locality of the arbitrary retained SAME-field seven-slot input.
Both actual high and low physical sections, P/R signs, and the common
phase/storage factor are preserved, including all full Fourier modes. -/
theorem homogeneousCoupledSevenInput_restriction (parameters : PhaseParameters) (lower upper length : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper)
    (field : CoupledSpace lower length lowerPositive lengthPositive) :
    originalBulkRestriction 7 lower upper included
      (homogeneousCoupledSevenInput parameters length lower lengthPositive lowerPositive field) =
    homogeneousCoupledSevenInput parameters length upper lengthPositive upperPositive
      (coupledEndpointRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field) := by
  let targetField := coupledEndpointRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field
  have sourceLaw := homogeneousCoupledSevenInput_sameSections parameters lower length lowerPositive (included.trans_lt upperBounded) lengthPositive field
  have targetLaw := homogeneousCoupledSevenInput_sameSections parameters upper length upperPositive upperBounded lengthPositive targetField
  apply lp.ext
  funext mode
  apply Lp.ext
  filter_upwards [originalBulkRestriction_ae 7 lower upper included
      (homogeneousCoupledSevenInput parameters length lower lengthPositive lowerPositive field),
    sourceLaw.filter_mono (ae_mono (collarMeasure_le lower upper included)), targetLaw,
    ae_restrict_mem measurableSet_Icc] with radius restricted source target inside
  have x := coupledEndpointRestriction_x_base parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included field ⟨radius,inside⟩ mode
  have xi := coupledEndpointRestriction_xi_base parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included field ⟨radius,inside⟩ mode
  have xClamp :
      sameCoupledXCoefficient parameters upper length upperPositive upperBounded lengthPositive targetField 0 (radialClamp upper upperBounded.le radius) mode =
      sameCoupledXCoefficient parameters lower length lowerPositive (included.trans_lt upperBounded) lengthPositive field 0
        (radialClamp lower (included.trans upperBounded.le) radius) mode := by
    simpa only [radialClamp_eq upper upperBounded.le radius inside,
      radialClamp_eq lower (included.trans upperBounded.le) radius ⟨included.trans inside.1,inside.2⟩] using x
  have xiClamp :
      sameCoupledXiCoefficient parameters upper length upperPositive upperBounded lengthPositive targetField 0 (radialClamp upper upperBounded.le radius) mode =
      sameCoupledXiCoefficient parameters lower length lowerPositive (included.trans_lt upperBounded) lengthPositive field 0
        (radialClamp lower (included.trans upperBounded.le) radius) mode := by
    simpa only [radialClamp_eq upper upperBounded.le radius inside,
      radialClamp_eq lower (included.trans upperBounded.le) radius ⟨included.trans inside.1,inside.2⟩] using xi
  have sameVector := congrArg₂ (rawPhysicalSevenVector radius mode) xClamp xiClamp
  have sameStored := congrArg₂ (fun (weight : ℝ) (value : ComplexEuclidean 7) => (weight : ℂ) • value)
    (restrictionLowRhoWeight parameters lower upper lowerPositive upperPositive included radius inside mode) sameVector
  exact (restricted mode).trans ((source mode).trans (sameStored.symm.trans (target mode).symm))

end Grad.AnnularRestriction
