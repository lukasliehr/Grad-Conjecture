import ANR6HighCompactTest

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

open Set MeasureTheory
open scoped ContDiff BigOperators

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.NonlinearDivision

def excludedTestValue (modes : Finset ℤ) (field : SpatialPlane → ComplexEuclidean 1) :
    SpatialPlane → ComplexEuclidean 1 :=
  fun point => field point - ∑ mode ∈ modes, angularProjectionValue mode field point

theorem excludedTest_smooth (modes : Finset ℤ) (field : SpatialPlane → ComplexEuclidean 1)
    (smooth : ContDiff ℝ ∞ field) : ContDiff ℝ ∞ (excludedTestValue modes field) :=
  smooth.sub (ContDiff.sum (fun mode _ => angularProjectionValue_smooth mode smooth))

private theorem selectedTest_compact_inside (modes : Finset ℤ)
    (field : SpatialPlane → ComplexEuclidean 1) (compact : HasCompactSupport field)
    (supported : tsupport field ⊆ openUnitDisk) :
    HasCompactSupport (fun point => ∑ mode ∈ modes, angularProjectionValue mode field point) ∧
      tsupport (fun point => ∑ mode ∈ modes, angularProjectionValue mode field point) ⊆ openUnitDisk := by
  induction modes using Finset.induction_on with
  | empty =>
    simp
    change IsCompact (tsupport (fun _ : SpatialPlane => (0 : ComplexEuclidean 1)))
    simp
  | @insert mode modes absent induction =>
    have current := angularProjection_compact_inside mode field compact supported
    have identity : (fun point => ∑ selected ∈ insert mode modes, angularProjectionValue selected field point) =
        (fun point => angularProjectionValue mode field point +
          ∑ selected ∈ modes, angularProjectionValue selected field point) := by
      funext point
      exact Finset.sum_insert absent
    rw [identity]
    exact ⟨current.1.add induction.1, (tsupport_add _ _).trans (Set.union_subset current.2 induction.2)⟩

theorem excludedTest_compact_inside (modes : Finset ℤ)
    (field : SpatialPlane → ComplexEuclidean 1) (compact : HasCompactSupport field)
    (supported : tsupport field ⊆ openUnitDisk) :
    HasCompactSupport (excludedTestValue modes field) ∧
      tsupport (excludedTestValue modes field) ⊆ openUnitDisk := by
  have selected := selectedTest_compact_inside modes field compact supported
  exact ⟨compact.sub selected.1, (tsupport_sub _ _).trans (Set.union_subset supported selected.2)⟩

private def closedPointValue (point : ClosedDisk) : ClosedJet 1 →ₗ[ℂ] ComplexEuclidean 1 where
  toFun field := field.value point
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem excludedTest_jet (modes : Finset ℤ)
    (field : SpatialPlane → ComplexEuclidean 1) (smooth : ContDiff ℝ ∞ field) :
    globalClosedJet (excludedTestValue modes field) (excludedTest_smooth modes field smooth) =
      excludedAngularJet modes (globalClosedJet field smooth) := by
  apply globalClosedJet_eq_of_restriction
  intro point
  change field point.val - ∑ mode ∈ modes, angularProjectionValue mode field point.val =
    closedPointValue point (globalClosedJet field smooth - selectedAngularJet modes (globalClosedJet field smooth))
  rw [map_sub, selectedAngularJet_eq, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro mode _
  exact congrArg (fun jet : ClosedJet 1 => jet.value point) (globalClosedJet_angular mode field smooth)

theorem highL2Projection_pairing (test : DiskL2 1) (field : highDiskL2) :
    inner ℂ (highL2Projection test) field.val = inner ℂ test field.val := by
  have lowZero : (∑ mode ∈ lowAngularModes, inner ℂ (diskMode mode test) field.val) = 0 := by
    apply Finset.sum_eq_zero
    intro mode low
    exact (diskMode_symmetric mode test field.val).trans
      ((congrArg (fun value : DiskL2 1 => inner ℂ test value) (field.property mode low)).trans (inner_zero_right _))
  exact (congrArg (fun value : DiskL2 1 => inner ℂ value field.val) (highL2Projection_apply test)).trans
    ((inner_sub_left _ _ _).trans
      ((congrArg (fun value : ℂ => inner ℂ test field.val - value)
        ((sum_inner lowAngularModes (fun mode => diskMode mode test) field.val).trans lowZero)).trans (sub_zero _)))

/-- The constructed AN18 solution satisfies its equation against every
compact smooth Cartesian vector test on the whole open disk. -/
theorem weakInverse_compact (parameter : ℝ) (source : highDiskL2)
    (test : SpatialPlane → ComplexEuclidean 1) (smooth : ContDiff ℝ ∞ test)
    (compact : HasCompactSupport test) (supported : tsupport test ⊆ openUnitDisk) :
    inner ℂ (closedL2Core (laplacianJet (globalClosedJet test smooth)))
        (highDiskBulk (highRobinWeakInverse parameter source)) =
      inner ℂ (closedL2Core (globalClosedJet test smooth)) (weakLaplacianValue parameter source) := by
  let projected := excludedTestValue lowAngularModes test
  have projectedSmooth := excludedTest_smooth lowAngularModes test smooth
  have projectedSupport := excludedTest_compact_inside lowAngularModes test compact supported
  have jetLaw := excludedTest_jet lowAngularModes test smooth
  have high : excludedAngularJet lowAngularModes (globalClosedJet projected projectedSmooth) =
      globalClosedJet projected projectedSmooth :=
    (congrArg (excludedAngularJet lowAngularModes) jetLaw).trans
      ((excludedAngularJet_idempotent lowAngularModes (globalClosedJet test smooth)).trans jetLaw.symm)
  have equation := weakInverse_high_compact parameter source projected projectedSmooth
    projectedSupport.1 projectedSupport.2 high
  have valueLaw : closedL2Core (globalClosedJet projected projectedSmooth) =
      highL2Projection (closedL2Core (globalClosedJet test smooth)) :=
    (congrArg closedL2Core jetLaw).trans (highL2Projection_core (globalClosedJet test smooth)).symm
  have laplacianLaw : closedL2Core (laplacianJet (globalClosedJet projected projectedSmooth)) =
      highL2Projection (closedL2Core (laplacianJet (globalClosedJet test smooth))) :=
    (congrArg (fun jet => closedL2Core (laplacianJet jet)) jetLaw).trans
      ((congrArg closedL2Core (laplacianJet_excluded lowAngularModes (globalClosedJet test smooth))).trans
        (highL2Projection_core (laplacianJet (globalClosedJet test smooth))).symm)
  have first := (congrArg (fun value : DiskL2 1 =>
      inner ℂ value (highDiskBulk (highRobinWeakInverse parameter source))) laplacianLaw).trans
    (highL2Projection_pairing _ (highBulkInto (highRobinWeakInverse parameter source)))
  have second := (congrArg (fun value : DiskL2 1 => inner ℂ value (weakLaplacianValue parameter source)) valueLaw).trans
    (highL2Projection_pairing _ ⟨weakLaplacianValue parameter source, weakLaplacianValue_high parameter source⟩)
  exact first.symm.trans (equation.trans second)

end Grad.CircularHighRegularity
