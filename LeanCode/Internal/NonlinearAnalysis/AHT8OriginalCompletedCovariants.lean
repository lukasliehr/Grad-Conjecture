import AHT7ActualOriginalKernelFamilies

noncomputable section
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularKernelL2
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.PhaseAlgebra Grad.BoundaryLift Grad.AnnularKernelContinuity

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact)

def originalCovariantAction (power : ℕ) : DivisionRow 7 lower →L[ℂ] DivisionRow 3 lower :=
  completedBulkKernel parameters power lower (collarRadius lower positive bounded)
    (collarRadius_continuous lower positive bounded)
    (originalCovariantFamily parameters L compact lower positive bounded state)
    (originalCovariantFamily_measurable parameters L compact lower positive bounded state)
    (originalKernelConstant parameters L compact lower positive power * state.val.size power)
    (originalCovariantFamily_moment parameters L compact lower positive bounded state power)

def originalRotatedAction (power : ℕ) : DivisionRow 7 lower →L[ℂ] DivisionRow 3 lower :=
  completedBulkKernel parameters power lower (collarRadius lower positive bounded)
    (collarRadius_continuous lower positive bounded)
    (originalRotatedFamily parameters L compact lower positive bounded state)
    (originalRotatedFamily_measurable parameters L compact lower positive bounded state)
    (originalKernelConstant parameters L compact lower positive power * state.val.size power)
    (originalRotatedFamily_moment parameters L compact lower positive bounded state power)

theorem originalCovariantAction_bound (power : ℕ) (field : DivisionRow 7 lower) :
    ‖originalCovariantAction parameters L compact lower positive bounded state power field‖ ≤
      originalKernelConstant parameters L compact lower positive power * state.val.size power * ‖field‖ :=
  completedBulkKernel_bound _ _ _ _ _ _ _ _ _ _

theorem originalRotatedAction_bound (power : ℕ) (field : DivisionRow 7 lower) :
    ‖originalRotatedAction parameters L compact lower positive bounded state power field‖ ≤
      originalKernelConstant parameters L compact lower positive power * state.val.size power * ‖field‖ :=
  completedBulkKernel_bound _ _ _ _ _ _ _ _ _ _

theorem originalCovariantAction_physical (power : ℕ) (field : DivisionRow 7 lower) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1), ∀ mode,
      HasSum (fun shift => (originalCovariantFamily parameters L compact lower positive bounded state x).entry
        shift (twoFrequencyTranslation shift mode)
        (originalRowCoefficient parameters power lower field x (twoFrequencyTranslation shift mode)))
        (originalRowCoefficient parameters power lower
          (originalCovariantAction parameters L compact lower positive bounded state power field) x mode) := by
  apply completedBulkKernel_physical parameters power lower positive
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x inside
  exact collarRadius_literal lower positive bounded x inside

theorem originalRotatedAction_physical (power : ℕ) (field : DivisionRow 7 lower) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1), ∀ mode,
      HasSum (fun shift => (originalRotatedFamily parameters L compact lower positive bounded state x).entry
        shift (twoFrequencyTranslation shift mode)
        (originalRowCoefficient parameters power lower field x (twoFrequencyTranslation shift mode)))
        (originalRowCoefficient parameters power lower
          (originalRotatedAction parameters L compact lower positive bounded state power field) x mode) := by
  apply completedBulkKernel_physical parameters power lower positive
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x inside
  exact collarRadius_literal lower positive bounded x inside

/-- Both actual original seven-slot reconstruction operators act on all
completed original annular data. The same physical low ball works at every
grade, and the high physical norm enters only once. -/
theorem originalCompletedCovariants_oneHigh :
    ∀ power, ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (state : AnnularReconstructionState parameters L compact) (field : DivisionRow 7 lower),
      ‖originalCovariantAction parameters L compact lower positive bounded state power field‖ +
        ‖originalRotatedAction parameters L compact lower positive bounded state power field‖ ≤
          constant * (1 + Grad.GaugeCoefficients.Physical.Allocation.physicalBudget parameters
            state.val.field state.val.rho state.val.epsilon (power + 7)) * ‖field‖ := by
  intro power
  refine ⟨2 * originalKernelConstant parameters L compact lower positive power,
    mul_nonneg (by norm_num) (originalKernelConstant_nonnegative parameters L compact lower positive power), ?_⟩
  intro current field
  exact (add_le_add (originalCovariantAction_bound parameters L compact lower positive bounded current power field)
    (originalRotatedAction_bound parameters L compact lower positive bounded current power field)).trans_eq (by
      change _ + _ = 2 * originalKernelConstant parameters L compact lower positive power * current.val.size power * ‖field‖
      ring)

end Grad.AnnularKernelL2
