import GC18FourierMean
import DivisionUniqueness

noncomputable section

set_option maxHeartbeats 1200000

open Set Filter
open scoped Topology BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.NonlinearDivision

/-- The full-cell physical coefficient is continuous on the closed disk;
the uniform majorant is the original weighted coefficient l1 norm. -/
theorem fourierEvaluation_continuous {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (coefficient : Coefficient L sigma gamma ell 0 input output) (angle : ℝ) :
    Continuous (fun point : ClosedDisk => fourierEvaluation coefficient angle point) := by
  apply continuous_tsum
    (fun cell : ℤ => (coefficientValue coefficient cell).continuous.const_smul (fourierPhase cell angle))
    (coordinate_norm_summable coefficient.val zeroDerivativeIndex)
  intro cell point
  change ‖fourierPhase cell angle • coefficientValue coefficient cell point‖ ≤ _
  rw [norm_smul, fourierPhase_norm, one_mul]
  exact coefficientValue_point_norm_le admissible coefficient cell point

theorem coefficientPhysicalValue_continuous {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (grade : ℕ) (angle : ℝ) :
    Continuous (fun point : ClosedDisk => coefficientPhysicalValue (family grade) angle point) := by
  simp_rw [coherent_physicalValue family coherent]
  exact fourierEvaluation_continuous admissible (family 0) angle

/-- A continuous identity on the punctured closed disk extends to the axis,
using the explicit off-axis sequence in the original disk. -/
theorem continuous_closedDisk_eq_of_offAxis {Target : Type*} [TopologicalSpace Target] [T2Space Target]
    (first second : ClosedDisk → Target) (firstContinuous : Continuous first)
    (secondContinuous : Continuous second)
    (offAxis : ∀ point : ClosedDisk, point.val ≠ 0 → first point = second point)
    (point : ClosedDisk) : first point = second point := by
  by_cases axis : point.val = 0
  · have atOrigin : point = closedOrigin := Subtype.ext axis
    rw [atOrigin]
    have agree : ∀ index, first (axisSequence index) = second (axisSequence index) :=
      fun index => offAxis _ (axisSequence_offAxis index)
    exact tendsto_nhds_unique
      (((firstContinuous.tendsto closedOrigin).comp axisSequence_tendsto).congr agree)
      ((secondContinuous.tendsto closedOrigin).comp axisSequence_tendsto)
  · exact offAxis point axis

end Grad.GaugeCoefficients.Physical.RadialLedger
