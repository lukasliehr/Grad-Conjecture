import ARW10UniformOuterGain
import ABF3ActualFiniteSmoothInverse
import QO5EulerMean

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.ActualSmoothRobin
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.ActualOuterCollar Grad.SourceCollarRestriction
open Grad.SourceCollarDivision Grad.BoundaryTrace Grad.NonlinearRange

/-- Exact actual inverse radial representative agrees on the entire closed collar. -/
theorem sameH1_radial_value (parameter : ℝ) (source : highDiskL2) (solution : ClosedJet 1)
    (same : diskCoreInto solution = (highRobinWeakInverse parameter source).val)
    (mode : ℤ) (radius : ℝ) (inside : radius ∈ Icc (1 / 2 : ℝ) 1) :
    Grad.ActualRadialWords.actualProfile mode parameter source radius =
      radialCoefficientJet (originalPolarValue solution) mode 0 radius := by
  unfold Grad.ActualRadialWords.actualProfile actualRadialValue
  rw [← same]
  exact radialSection_core_value mode solution radius inside

/-- Robin recovery at r=1 for the genuine radial Fourier coefficient of
any smooth representative of the same full H1 inverse. -/
theorem sameH1_high_radial_robin (parameter : ℝ) (source : highDiskL2) (solution : ClosedJet 1)
    (same : diskCoreInto solution = (highRobinWeakInverse parameter source).val)
    (mode : ℤ) (high : mode ∉ lowAngularModes) :
    radialCoefficientJet (originalPolarValue solution) mode 1 1 +
      (2 : ℝ) • radialCoefficientJet (originalPolarValue solution) mode 0 1 = 0 := by
  have actual := weakInverse_literal_robin (1 / 2) (by norm_num) (by norm_num)
    parameter source mode high
  have equal : EqOn (radialCoefficientJet (originalPolarValue solution) mode 0)
      (Grad.ActualRadialWords.actualProfile mode parameter source) (Icc (1 / 2 : ℝ) 1) :=
    fun radius inside => (sameH1_radial_value parameter source solution same mode radius inside).symm
  have transferred := actual.congr equal (equal (by norm_num : (1 : ℝ) ∈ Icc (1 / 2 : ℝ) 1))
  have classicalDerivative := (radialCoefficientJet_hasDerivAt _ (originalPolarValue_smooth solution) mode 0 1).hasDerivWithinAt (s := Icc (1 / 2 : ℝ) 1)
  have unique := uniqueDiffOn_Icc (by norm_num : (1 / 2 : ℝ) < 1) 1 (by norm_num)
  have law := (classicalDerivative.derivWithin unique).symm.trans (transferred.derivWithin unique)
  change radialCoefficientJet (originalPolarValue solution) mode 1 1 =
    -(2 : ℝ) • Grad.ActualRadialWords.actualProfile mode parameter source 1 at law
  rw [sameH1_radial_value parameter source solution same mode 1 (by norm_num)] at law
  rw [law, neg_smul, neg_add_cancel]

end Grad.ActualSmoothRobin
