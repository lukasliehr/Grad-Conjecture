import AKN9ActualWeightedBulkRows
import SCS2PolarRows

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.ExhaustionSourceAllocation

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.SourceCollarDivision
open Grad.NonlinearRadial Grad.BoundaryTrace Grad.SourceCollarCoefficients

theorem sourceTiltRow_ae {dimension grade depth power : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (flat : ∀ cell, VanishingJets depth (field.val cell)) (paid : depth + power + 2 ≤ grade)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (division : ℕ) (vanishing : division + 2 ≤ depth) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      sourceTiltRow parameters field flat paid lower positive bounded division vanishing mode radius =
        ((annularFrequency mode.1 mode.2 : ℂ) ^ power) •
          (Real.sqrt radius • (sourceTiltFactor lower division radius •
            sourceCircleCoefficient parameters mode.2 (field.val mode.2) radius mode.1)) := by
  apply ae_all_iff.mpr
  intro mode
  filter_upwards [Lp.coeFn_smul ((annularFrequency mode.1 mode.2 : ℂ) ^ power)
      (radialToLp lower _ (sourceTiltRadialValue_continuous parameters mode.2 (field.val mode.2) lower positive division mode.1)),
    radialToLp_ae lower _ (sourceTiltRadialValue_continuous parameters mode.2 (field.val mode.2) lower positive division mode.1)]
    with radius scaled literal
  change sourceTiltModeLp parameters field lower positive division power mode radius = _
  rw [sourceTiltModeLp, scaled, Pi.smul_apply, literal]
  rfl

theorem sourceTiltRow_compatible {dimension grade depth power : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (flat : ∀ cell, VanishingJets depth (field.val cell)) (paid : depth + power + 2 ≤ grade)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (division : ℕ) (vanishing : division + 2 ≤ depth) :
    RadialRowsCompatible lower power
      (sourceTiltRow parameters field flat paid lower positive bounded division vanishing)
      (sourceTiltRow (power := 0) parameters field flat (by omega : depth + 0 + 2 ≤ grade)
        lower positive bounded division vanishing) := by
  intro mode
  change sourceTiltModeLp parameters field lower positive division power mode =
    ((annularFrequency mode.1 mode.2 : ℂ) ^ power) • sourceTiltModeLp parameters field lower positive division 0 mode
  simp only [sourceTiltModeLp, pow_zero, one_smul]

theorem sourceTiltRow_grade_independent {dimension firstGrade secondGrade depth power : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (flat : ∀ cell, VanishingJets depth (field.val cell))
    (firstPaid : depth + power + 2 ≤ firstGrade) (secondPaid : depth + power + 2 ≤ secondGrade)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (division : ℕ) (vanishing : division + 2 ≤ depth) :
    sourceTiltRow parameters field flat firstPaid lower positive bounded division vanishing =
      sourceTiltRow parameters field flat secondPaid lower positive bounded division vanishing := by
  apply lp.ext
  rfl

end Grad.ExhaustionSourceAllocation
