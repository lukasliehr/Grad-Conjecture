import AHW5ExactNormalizedFirstRowElimination

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse

/-- Restore Rxi and xi from exactly the normalized second and fourth slots. -/
def radialOriginalSevenKernel (parameters : PhaseParameters) (r : RadialPoint) : RadialKernel parameters r 7 7 :=
  constantMatrixKernel (radialKernelParameters parameters r) 7 7 (radialSevenSlotNormalization r.val⁻¹)

theorem radialSevenSlotKernel_original_inverse (parameters : PhaseParameters) (r : RadialPoint) (positive : 0 < r.val) :
    fullKernelComposition (radialSevenSlotKernel parameters r) (radialOriginalSevenKernel parameters r) =
      fullIdentityKernel (radialKernelParameters parameters r) 7 := by
  unfold radialSevenSlotKernel radialOriginalSevenKernel
  rw [constantMatrixKernel_comp]
  have identity : (radialSevenSlotNormalization r.val).comp (radialSevenSlotNormalization r.val⁻¹) =
      ContinuousLinearMap.id ℂ (ComplexEuclidean 7) := by
    apply ContinuousLinearMap.ext
    intro value
    apply PiLp.ext
    intro component
    have nonzero : (r.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
    fin_cases component <;>
      simp [ContinuousLinearMap.comp_apply, radialSevenSlotNormalization_apply, nonzero]
  rw [identity]
  exact constantMatrixKernel_id _ _

def assembledOriginalEightTrace (parameters : PhaseParameters) (r : RadialPoint) (angular cell : ℕ)
    (x : NegativeTrace (radialKernelParameters parameters r) angular cell 1)
    (input : NegativeTrace (radialKernelParameters parameters r) angular cell 8) :
    NegativeTrace (radialKernelParameters parameters r) angular cell 7 :=
  fullNegativeKernelAction (radialKernelParameters parameters r) angular cell (radialOriginalSevenKernel parameters r)
    (assembledNormalizedEightTrace (radialKernelParameters parameters r) angular cell x input)

theorem assembledOriginalEightTrace_normalization (parameters : PhaseParameters) (r : RadialPoint)
    (positive : 0 < r.val) (angular cell : ℕ)
    (x : NegativeTrace (radialKernelParameters parameters r) angular cell 1)
    (input : NegativeTrace (radialKernelParameters parameters r) angular cell 8) :
    fullNegativeKernelAction (radialKernelParameters parameters r) angular cell (radialSevenSlotKernel parameters r)
      (assembledOriginalEightTrace parameters r angular cell x input) =
      assembledNormalizedEightTrace (radialKernelParameters parameters r) angular cell x input := by
  unfold assembledOriginalEightTrace
  change ((fullNegativeKernelAction (radialKernelParameters parameters r) angular cell (radialSevenSlotKernel parameters r)).comp
    (fullNegativeKernelAction (radialKernelParameters parameters r) angular cell (radialOriginalSevenKernel parameters r))) _ = _
  rw [← fullNegativeKernelAction_comp, radialSevenSlotKernel_original_inverse parameters r positive,
    fullNegativeKernelAction_identity, ContinuousLinearMap.id_apply]

/-- The literal original first force equation, after Q and the original P.
The seven inputs are restored to physical Rxi and xi before reconstruction. -/
def originalEightFirstForceEquation (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) (positive : 0 < r.val) (angular cell : ℕ)
    (x : NegativeTrace (radialKernelParameters parameters r) angular cell 1)
    (input : NegativeTrace (radialKernelParameters parameters r) angular cell 8) : Prop :=
  let p := radialKernelParameters parameters r
  let original := assembledOriginalEightTrace parameters r angular cell x input
  fullNegativeKernelAction p angular cell (highAngularKernel p 1)
    (fullNegativeKernelAction p angular cell (angularMeanFreeKernel p 1)
      (-fullNegativeKernelAction p angular cell (coordinateProjectionKernel p 3 0)
        (fullNegativeKernelAction p angular cell
          (radialRotatedCovariantKernel parameters L compact state.val.val r state.val.property positive) original) +
       fullNegativeKernelAction p angular cell (radialRetainedForceKernel parameters L compact state.val.val r)
        (fullNegativeKernelAction p angular cell
          (radialCovariantKernel parameters L compact state.val.val r state.val.property positive) original) +
       fullNegativeKernelAction p angular cell (eightInputSlotKernel p 0) input)) =
  fullNegativeKernelAction p angular cell (highAngularKernel p 1)
    (fullNegativeKernelAction p angular cell (eightInputSlotKernel p 7) input)

/-- Exact AI8 equivalence for the original physical AHS row and the same actual inverse.
No derivative of any source is introduced or removed. -/
theorem originalEightFirstForceEquation_iff (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) (positive : 0 < r.val) (angular cell : ℕ)
    (x : NegativeTrace (radialKernelParameters parameters r) angular cell 1)
    (high : IsHighAngularTrace (radialKernelParameters parameters r) angular cell x)
    (input : NegativeTrace (radialKernelParameters parameters r) angular cell 8) :
    originalEightFirstForceEquation parameters L compact state r positive angular cell x input ↔
      x = fullNegativeKernelAction (radialKernelParameters parameters r) angular cell
        (radialEliminatedXKernel parameters L compact state r) input := by
  unfold originalEightFirstForceEquation
  dsimp only
  rw [radialRetainedFirstRow_equation_iff, radialRetainedFirstRowKernel_normalized,
    fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    assembledOriginalEightTrace_normalization parameters r positive]
  simpa only [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply] using
    normalizedFirstRow_elimination_iff parameters L compact state r angular cell x high input

end Grad.AnnularReconstruction
