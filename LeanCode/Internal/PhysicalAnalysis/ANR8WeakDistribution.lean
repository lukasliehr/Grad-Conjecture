import ANR7ArbitraryCompactTest

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory
open scoped ContDiff

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.NonlinearDivision Grad.GenericCarriers

private theorem scalarVector_support (test : SpatialPlane → ℝ) (vector : PhysicalValue 1) :
    tsupport (fun point => test point • vector) ⊆ tsupport test := by
  apply closure_mono
  intro point nonzero
  change test point ≠ 0
  intro zero
  apply nonzero
  dsimp only
  rw [zero, zero_smul]

theorem closedL2_inner_scalar (jet : ClosedJet 1) (test : SpatialPlane → ℝ)
    (vector : PhysicalValue 1) (literal : ∀ point : ClosedDisk, jet.value point = test point.val • vector)
    (field : DiskL2 1) :
    inner ℂ (closedL2Core jet) field =
      ∫ point in openUnitDisk, test point • inner ℂ vector (field point) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [closedContinuousToDiskL2_ae jet.value,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point representative inside
  change inner ℂ (closedContinuousToDiskL2 jet.value point) (field point) = _
  rw [representative, closedDiskLift, dif_pos (openDiskMembershipClosed point inside), literal]
  exact inner_smul_left_eq_smul _ _ _

theorem scalarVector_laplacian (test : SpatialPlane → ℝ) (smooth : ContDiff ℝ ∞ test)
    (vector : PhysicalValue 1) (point : ClosedDisk) :
    (laplacianJet (globalClosedJet (fun source => test source • vector) (smooth.smul contDiff_const))).value point =
      testLaplacian test point.val • vector := by
  rw [laplacianJet_value]
  change closedDerivative (globalClosedJet (fun source => test source • vector) (smooth.smul contDiff_const))
      2 (fun _ => 0) point +
    closedDerivative (globalClosedJet (fun source => test source • vector) (smooth.smul contDiff_const))
      2 (fun _ => 1) point = _
  rw [globalClosedJet_derivative, globalClosedJet_derivative]
  simp only [cartesianDerivative]
  rw [iteratedFDeriv_smul_const_apply
    (smooth.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
  change Grad.WeakTesting.orderedTestDerivative 2 (fun _ => 0) test point.val • vector +
      Grad.WeakTesting.orderedTestDerivative 2 (fun _ => 1) test point.val • vector = _
  exact (add_smul _ _ _).symm

/-- The actual variational inverse satisfies the full Cartesian distribution
law Δz=k²Bz−F, against arbitrary compact tests on the original full disk. -/
theorem weakInverse_distribution (parameter : ℝ) (source : highDiskL2) :
    HasDiskWeakLaplacian (highDiskBulk (highRobinWeakInverse parameter source))
      (weakLaplacianValue parameter source) := by
  intro vector test smooth compact supported
  have vectorSmooth := smooth.smul (contDiff_const : ContDiff ℝ ∞ (fun _ : SpatialPlane => vector))
  have vectorCompact : HasCompactSupport (fun point => test point • vector) := compact.smul_right
  have vectorSupported := (scalarVector_support test vector).trans supported
  have equation := weakInverse_compact parameter source (fun point => test point • vector)
    vectorSmooth vectorCompact vectorSupported
  have valueLiteral := closedL2_inner_scalar
    (globalClosedJet (fun point => test point • vector) vectorSmooth) test vector (fun _ => rfl)
    (weakLaplacianValue parameter source)
  have laplacianLiteral := closedL2_inner_scalar
    (laplacianJet (globalClosedJet (fun point => test point • vector) vectorSmooth))
    (testLaplacian test) vector (scalarVector_laplacian test smooth vector)
    (highDiskBulk (highRobinWeakInverse parameter source))
  exact valueLiteral.symm.trans (equation.symm.trans laplacianLiteral)

end Grad.CircularHighRegularity
