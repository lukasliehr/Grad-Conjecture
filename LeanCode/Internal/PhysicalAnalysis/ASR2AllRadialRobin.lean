import ASR1SmoothRadialRobin

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.ActualSmoothRobin
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.ActualOuterCollar Grad.SourceCollarRestriction
open Grad.SourceCollarDivision Grad.BoundaryTrace Grad.NonlinearRange

theorem sameH1_low_projection_zero (parameter : ℝ) (source : highDiskL2) (solution : ClosedJet 1)
    (same : diskCoreInto solution = (highRobinWeakInverse parameter source).val)
    (mode : ℤ) (low : mode ∈ lowAngularModes) : angularClosedJet mode solution = 0 := by
  have bulk : closedL2Core solution = highDiskBulk (highRobinWeakInverse parameter source) :=
    (Grad.CircularHighWeak.diskBulk_core solution).symm.trans (congrArg diskBulk same)
  apply closedL2Core_injective
  exact (diskMode_core mode solution).symm.trans
    ((congrArg (diskMode mode) bulk).trans
      ((highDiskBulk_spectral (highRobinWeakInverse parameter source) mode low).trans closedL2Core.map_zero.symm))

theorem sameH1_low_radial_zero (parameter : ℝ) (source : highDiskL2) (solution : ClosedJet 1)
    (same : diskCoreInto solution = (highRobinWeakInverse parameter source).val)
    (mode : ℤ) (low : mode ∈ lowAngularModes) :
    radialCoefficientJet (originalPolarValue solution) mode 0 1 = 0 ∧
      radialCoefficientJet (originalPolarValue solution) mode 1 1 = 0 := by
  have projected := sameH1_low_projection_zero parameter source solution same mode low
  have equal : EqOn (radialCoefficientJet (originalPolarValue solution) mode 0)
      (fun _ : ℝ => (0 : ComplexEuclidean 1)) (Icc (1 / 2 : ℝ) 1) := by
    intro radius inside
    rw [radialCoefficient_projection_value solution mode radius (by linarith [inside.1]) inside.2, projected]
    rfl
  have endpoint : (1 : ℝ) ∈ Icc (1 / 2 : ℝ) 1 := by norm_num
  have constant := (hasDerivAt_const (1 : ℝ) (0 : ComplexEuclidean 1)).hasDerivWithinAt (s := Icc (1 / 2 : ℝ) 1)
  have transferred := constant.congr equal (equal endpoint)
  have classicalDerivative := (radialCoefficientJet_hasDerivAt _ (originalPolarValue_smooth solution) mode 0 1).hasDerivWithinAt (s := Icc (1 / 2 : ℝ) 1)
  have unique := uniqueDiffOn_Icc (by norm_num : (1 / 2 : ℝ) < 1) 1 endpoint
  exact ⟨equal endpoint, (classicalDerivative.derivWithin unique).symm.trans (transferred.derivWithin unique)⟩

theorem sameH1_all_radial_robin (parameter : ℝ) (source : highDiskL2) (solution : ClosedJet 1)
    (same : diskCoreInto solution = (highRobinWeakInverse parameter source).val) (mode : ℤ) :
    radialCoefficientJet (originalPolarValue solution) mode 1 1 +
      (2 : ℝ) • radialCoefficientJet (originalPolarValue solution) mode 0 1 = 0 := by
  by_cases low : mode ∈ lowAngularModes
  · obtain ⟨value, slope⟩ := sameH1_low_radial_zero parameter source solution same mode low
    rw [value, slope, smul_zero, add_zero]
  · exact sameH1_high_radial_robin parameter source solution same mode low

end Grad.ActualSmoothRobin
