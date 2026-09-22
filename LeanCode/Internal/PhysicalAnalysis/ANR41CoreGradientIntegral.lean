import ANR40IntegratedPolarGradient

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.NonlinearQuotient
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.BoundaryTrace

private theorem coreGradient_direction (direction : Fin 2) (test : SpatialPlane → ComplexEuclidean 1)
    (smooth : ContDiff ℝ ∞ test) (field : ClosedJet 1) :
    inner ℂ (diskPartial direction (diskCoreInto (globalClosedJet test smooth)))
      (diskPartial direction (diskCoreInto field)) =
    ∫ point in openUnitDisk, inner ℂ (spatialPartial direction test point)
      (spatialPartial direction (smoothClosedExtension field) point) := by
  have actual := closedL2_inner_representatives (partialJet direction (globalClosedJet test smooth)) (partialJet direction field)
    (spatialPartial direction test) (spatialPartial direction (smoothClosedExtension field))
    (fun point => partialJet_global_value test smooth direction point)
    (by
      intro point
      have identity := partialJet_global_value (smoothClosedExtension field) (smoothClosedExtension_smooth field) direction point
      rw [smoothClosedExtension_restricts] at identity
      exact identity)
  exact (congrArg₂ (fun first second : DiskL2 1 => inner ℂ first second)
    (diskPartial_core direction (globalClosedJet test smooth)) (diskPartial_core direction field)).trans actual

theorem diskCore_gradient_integral (test : SpatialPlane → ComplexEuclidean 1)
    (smooth : ContDiff ℝ ∞ test) (field : ClosedJet 1) :
    inner ℂ (diskGradX (diskCoreInto (globalClosedJet test smooth))) (diskGradX (diskCoreInto field)) +
      inner ℂ (diskGradY (diskCoreInto (globalClosedJet test smooth))) (diskGradY (diskCoreInto field)) =
    ∫ point in openUnitDisk, cartesianGradientPairing test (smoothClosedExtension field) point := by
  have coordinateIntegrable (direction : Fin 2) : IntegrableOn (fun point =>
      inner ℂ (spatialPartial direction test point) (spatialPartial direction (smoothClosedExtension field) point)) openUnitDisk := by
    have continuous : Continuous (fun point => inner ℂ (spatialPartial direction test point)
        (spatialPartial direction (smoothClosedExtension field) point)) := (spatialPartial_smooth direction smooth).continuous.inner
      (spatialPartial_smooth direction (smoothClosedExtension_smooth field)).continuous
    have compact : IsCompact closedUnitDisk := by
      rw [closedUnitDisk_eq_closedBall]
      exact isCompact_closedBall _ _
    have closed : IntegrableOn (fun point => inner ℂ (spatialPartial direction test point)
        (spatialPartial direction (smoothClosedExtension field) point)) closedUnitDisk :=
      continuous.continuousOn.integrableOn_compact compact
    exact closed.mono_set (fun point inside => openDiskMembershipClosed point inside)
  have integral := integral_add (coordinateIntegrable 0) (coordinateIntegrable 1)
  have sum := congrArg₂ (fun first second : ℂ => first + second)
    (coreGradient_direction 0 test smooth field) (coreGradient_direction 1 test smooth field)
  exact sum.trans integral.symm

theorem boundaryCharacter_gradient_polar (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (smooth : ContDiff ℝ ∞ test) (away : (0 : ℝ) ∉ tsupport test) (field : ClosedJet 1) :
    inner ℂ (diskGradX (diskCoreInto (boundaryCharacterJet mode vector test smooth away))) (diskGradX (diskCoreInto field)) +
      inner ℂ (diskGradY (diskCoreInto (boundaryCharacterJet mode vector test smooth away))) (diskGradY (diskCoreInto field)) =
    (2 * Real.pi) • ∫ radius in Icc (0 : ℝ) 1,
      (radius * deriv test radius) • inner ℂ vector (radialCoefficientJet (originalPolarValue field) mode 1 radius) +
      (test radius * (mode : ℝ) ^ 2 / radius) • inner ℂ vector (radialCoefficientJet (originalPolarValue field) mode 0 radius) := by
  have coreLaw := diskCore_gradient_integral (radialTestLift mode vector test)
    (radialTestLift_smooth_away_axis mode vector test smooth away) field
  have polar := closedDisk_polar_complex (cartesianGradientPairing (radialTestLift mode vector test) (smoothClosedExtension field))
    (cartesianGradientPairing_continuous _ _ (radialTestLift_smooth_away_axis mode vector test smooth away)
      (smoothClosedExtension_smooth field))
  rw [Measure.restrict_congr_set closedUnitDisk_ae_openUnitDisk] at polar
  refine coreLaw.trans (polar.trans ?_)
  rw [← integral_smul]
  apply integral_congr_ae
  have interior : ∀ᵐ radius ∂volume.restrict (Icc (0 : ℝ) 1), radius ∈ Ioo (0 : ℝ) 1 := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [interior] with radius inside
  rw [integral_smul]
  exact character_gradient_angle mode vector test smooth away field radius inside.1

end Grad.CircularHighRegularity
