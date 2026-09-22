import AKO2ActualLowIncomingLogBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped ENNReal BigOperators
namespace Grad.AnnularIncomingIntegrability
open Grad.ClosedJets Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.AnnularReconstruction Grad.AnnularRestriction
open Grad.AnnularGrades Grad.AnnularTiltedReference Grad.CircularHighWeak
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)

/-- SAME r^-9/4 Wxi representative, with the original b decoder. -/
def highIncomingRepresentative (field : annularEnergySpace lower length positive) (mode : HighAnnularMode) : C(ℝ, ComplexEuclidean 1) :=
  radialSectionExtension 1 lower bounded.le
    (weightedRadialSection 1 lower positive bounded (annularModeRadialH1 lower length positive mode (bEnergyDecode lower length positive field)))

theorem highIncomingRepresentative_stored (field : annularEnergySpace lower length positive) (mode : HighAnnularMode) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), highIncomingRepresentative lower length positive bounded field mode radius =
      reciprocalRadialWeight lower (fun _ => 1) radius •
        annularEnergyValue lower length positive (bEnergyDecode lower length positive field) mode radius := by
  have sectionLaw := radialSectionL2_ae 1 lower positive bounded.le
    (weightedRadialSection 1 lower positive bounded (annularModeRadialH1 lower length positive mode (bEnergyDecode lower length positive field)))
  rw [highEnergySection_bulk] at sectionLaw
  filter_upwards [sectionLaw,radialOrdinary_ae 1 lower positive
    (annularEnergyValue lower length positive (bEnergyDecode lower length positive field) mode)] with radius sectionLaw ordinary
  exact sectionLaw.trans ordinary

/-- Grade insertion is transported through the actual b decoder and radial
energy coordinate; equality is on the SAME original completed graph. -/
theorem insertedHigh_radial_mode (field weighted : annularEnergySpace lower length positive)
    (same : ∀ mode : HighAnnularMode, weighted.val mode =
      (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 : ℂ) • field.val mode)
    (mode : HighAnnularMode) :
    annularEnergyRadial lower length positive (bEnergyDecode lower length positive weighted) mode =
      (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 : ℂ) •
        annularEnergyRadial lower length positive (bEnergyDecode lower length positive field) mode := by
  change scalarRadialMap lower (annularRadialMassRatio lower length positive mode) (2 / 3)
      (annularRadialMassRatio_bound lower length positive mode)
      (annularModeMass lower ((bEnergyDecode lower length positive weighted).val mode)) = _
  have decoded : (bEnergyDecode lower length positive weighted).val mode =
      (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 : ℂ) •
        (bEnergyDecode lower length positive field).val mode := by
    rw [bEnergyDecode,annularEnergyDiagonal_apply,annularEnergyDiagonal_apply,same mode,smul_comm]
  rw [decoded,map_smul,map_smul]
  rfl

/-- The genuine radial coordinate stores exactly (2/r) times the weighted
value; this identity is only asserted almost everywhere for the L2 coordinates. -/
theorem highIncomingRadial_stored (field : annularEnergySpace lower length positive) (mode : HighAnnularMode) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      annularEnergyRadial lower length positive (bEnergyDecode lower length positive field) mode radius =
        annularRadialCurve lower positive radius •
          annularEnergyValue lower length positive (bEnergyDecode lower length positive field) mode radius := by
  rw [annularEnergyRadial_mode]
  exact collarScalar_ae 1 lower _ _

end Grad.AnnularIncomingIntegrability
