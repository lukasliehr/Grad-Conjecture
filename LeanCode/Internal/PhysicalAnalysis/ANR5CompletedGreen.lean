import ANR3CompactGreen

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory
open scoped ContDiff

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.NonlinearQuotientBounds Grad.NonlinearRange

def diskPartial (direction : Fin 2) : diskGrade →L[ℂ] DiskL2 1 :=
  if direction = 0 then diskGradX else diskGradY

theorem diskBulk_core (field : ClosedJet 1) : diskBulk (diskCoreInto field) = closedL2Core field := by
  change diskCoordinate ⟨(0, 0), by decide⟩ (diskCoreInto field) = _
  rw [diskCoordinate_core]
  change closedContinuousToDiskL2 (closedMultiDerivative field (0, 0)) = _
  rw [closedMultiDerivative_zero]
  rfl

theorem diskPartial_core (direction : Fin 2) (field : ClosedJet 1) :
    diskPartial direction (diskCoreInto field) = closedL2Core (partialJet direction field) := by
  have firstWord : cartesianMultiIndexWord (1, 0) = (fun _ => 0) := by
    funext position; fin_cases position; rfl
  have secondWord : cartesianMultiIndexWord (0, 1) = (fun _ => 1) := by
    funext position; fin_cases position; rfl
  fin_cases direction
  · change diskGradX (diskCoreInto field) = closedL2Core (partialJet 0 field)
    exact (diskGradX_core field).trans
      (congrArg closedContinuousToDiskL2 (congrArg (closedDerivative field 1) firstWord))
  · change diskGradY (diskCoreInto field) = closedL2Core (partialJet 1 field)
    exact (diskGradY_core field).trans
      (congrArg closedContinuousToDiskL2 (congrArg (closedDerivative field 1) secondWord))

theorem globalClosedJet_partial (direction : Fin 2)
    (field : SpatialPlane → ComplexEuclidean 1) (smooth : ContDiff ℝ ∞ field) :
    partialJet direction (globalClosedJet field smooth) =
      globalClosedJet (spatialPartial direction field) (spatialPartial_smooth direction smooth) := by
  symm
  apply globalClosedJet_eq_of_restriction
  intro point
  exact (partialJet_global_value field smooth direction point).symm

theorem closedL2_inner_representatives (first second : ClosedJet 1)
    (firstValue secondValue : SpatialPlane → ComplexEuclidean 1)
    (firstLaw : ∀ point : ClosedDisk, first.value point = firstValue point.val)
    (secondLaw : ∀ point : ClosedDisk, second.value point = secondValue point.val) :
    inner ℂ (closedL2Core first) (closedL2Core second) =
      ∫ point in openUnitDisk, inner ℂ (firstValue point) (secondValue point) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [closedContinuousToDiskL2_ae first.value, closedContinuousToDiskL2_ae second.value,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point firstLiteral secondLiteral inside
  change inner ℂ (closedContinuousToDiskL2 first.value point) (closedContinuousToDiskL2 second.value point) = _
  rw [firstLiteral, secondLiteral, closedDiskLift, dif_pos (openDiskMembershipClosed point inside),
    closedDiskLift, dif_pos (openDiskMembershipClosed point inside), firstLaw, secondLaw]

/-- Compact Cartesian Green identity for the actual completed disk H1 graph.
Only the test is smooth; the unknown is an arbitrary accepted H1 element. -/
theorem completedGreen_direction (direction : Fin 2)
    (test : SpatialPlane → ComplexEuclidean 1) (smooth : ContDiff ℝ ∞ test)
    (compact : HasCompactSupport test) (supported : tsupport test ⊆ openUnitDisk)
    (field : diskGrade) :
    inner ℂ (closedL2Core (partialJet direction (globalClosedJet test smooth))) (diskPartial direction field) =
      -inner ℂ (closedL2Core (partialJet direction (partialJet direction (globalClosedJet test smooth))))
        (diskBulk field) := by
  apply isClosed_property diskCoreInto_denseRange
    (isClosed_eq
      ((innerSL ℂ (closedL2Core (partialJet direction (globalClosedJet test smooth)))).continuous.comp
        (diskPartial direction).continuous)
      (((innerSL ℂ (closedL2Core (partialJet direction (partialJet direction (globalClosedJet test smooth))))).continuous.comp
        diskBulk.continuous).neg)) _ field
  intro core
  have first := closedL2_inner_representatives
    (partialJet direction (globalClosedJet test smooth)) (partialJet direction core)
    (spatialPartial direction test) (spatialPartial direction (smoothClosedExtension core))
    (fun point => partialJet_global_value test smooth direction point)
    (by
      intro point
      have identity := partialJet_global_value (smoothClosedExtension core) (smoothClosedExtension_smooth core) direction point
      rw [smoothClosedExtension_restricts] at identity
      exact identity)
  have second := closedL2_inner_representatives
    (partialJet direction (partialJet direction (globalClosedJet test smooth))) core
    (spatialPartial direction (spatialPartial direction test)) (smoothClosedExtension core)
    (by
      intro point
      rw [globalClosedJet_partial, globalClosedJet_partial]
      rfl)
    (fun point => (smoothClosedExtension_value core point).symm)
  have classical := compactGreen_second direction test (smoothClosedExtension core) smooth
    (smoothClosedExtension_smooth core) compact supported
  exact (congrArg (fun value : DiskL2 1 =>
      inner ℂ (closedL2Core (partialJet direction (globalClosedJet test smooth))) value)
        (diskPartial_core direction core)).trans
    (first.trans (classical.trans ((congrArg Neg.neg second.symm).trans
      (congrArg (fun value : DiskL2 1 =>
        -inner ℂ (closedL2Core (partialJet direction (partialJet direction (globalClosedJet test smooth)))) value)
          (diskBulk_core core).symm))))


private theorem negative_inner_add {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (first second field : V) :
    -inner ℂ first field + -inner ℂ second field = -inner ℂ (first + second) field := by
  rw [inner_add_left, neg_add]

theorem completedGreen_laplacian
    (test : SpatialPlane → ComplexEuclidean 1) (smooth : ContDiff ℝ ∞ test)
    (compact : HasCompactSupport test) (supported : tsupport test ⊆ openUnitDisk)
    (field : diskGrade) :
    inner ℂ (closedL2Core (partialJet 0 (globalClosedJet test smooth))) (diskGradX field) +
      inner ℂ (closedL2Core (partialJet 1 (globalClosedJet test smooth))) (diskGradY field) =
      -inner ℂ (closedL2Core (Grad.NonlinearDivision.laplacianJet (globalClosedJet test smooth)))
        (diskBulk field) := by
  have first := completedGreen_direction 0 test smooth compact supported field
  have second := completedGreen_direction 1 test smooth compact supported field
  change inner ℂ (closedL2Core (partialJet 0 (globalClosedJet test smooth))) (diskGradX field) = _ at first
  change inner ℂ (closedL2Core (partialJet 1 (globalClosedJet test smooth))) (diskGradY field) = _ at second
  exact (congrArg₂ (fun first second : ℂ => first + second) first second).trans
    ((negative_inner_add _ _ (diskBulk field)).trans
      (congrArg (fun value : DiskL2 1 => -inner ℂ value (diskBulk field))
        (map_add closedL2Core
          (partialJet 0 (partialJet 0 (globalClosedJet test smooth)))
          (partialJet 1 (partialJet 1 (globalClosedJet test smooth)))).symm))

end Grad.CircularHighRegularity
