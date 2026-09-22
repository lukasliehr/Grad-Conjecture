import AHW4EliminatedKernelReferenceErrors

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse

theorem radialEliminationRightHandKernel_expansion (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) :
    radialEliminationRightHandKernel parameters L compact state r =
      fullKernelSub
        (fullKernelSub
          (fullKernelComposition (highAngularKernel (radialKernelParameters parameters r) 1)
            (eightInputSlotKernel (radialKernelParameters parameters r) 0))
          (fullKernelComposition (radialNormalizedRetainedFirstRowKernel parameters L compact state.val r)
            (knownEightToSevenKernel (radialKernelParameters parameters r))))
        (fullKernelComposition (highAngularKernel (radialKernelParameters parameters r) 1)
          (eightInputSlotKernel (radialKernelParameters parameters r) 7)) := by
  unfold radialEliminationRightHandKernel
  simp only [fullKernelSub, fullKernelComposition_add_inner, fullKernelComposition_neg_inner]
  rw [← fullKernelComposition_assoc, radialNormalizedRetainedFirstRowKernel_high_left]

/-- Actual algebraic first-row consumer, including every known source slot. -/
theorem radialEliminatedSevenKernel_firstRow (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) :
    fullKernelAdd
      (fullKernelComposition (radialNormalizedRetainedFirstRowKernel parameters L compact state.val r)
        (radialEliminatedSevenKernel parameters L compact state r))
      (fullKernelComposition (highAngularKernel (radialKernelParameters parameters r) 1)
        (eightInputSlotKernel (radialKernelParameters parameters r) 7)) =
      fullKernelComposition (highAngularKernel (radialKernelParameters parameters r) 1)
        (eightInputSlotKernel (radialKernelParameters parameters r) 0) := by
  have first : fullKernelComposition (radialNormalizedRetainedFirstRowKernel parameters L compact state.val r)
      (fullKernelComposition (coordinateInjectionKernel (radialKernelParameters parameters r) 7 0)
        (radialEliminatedXKernel parameters L compact state r)) =
      radialEliminationRightHandKernel parameters L compact state r := by
    have equation := radialEliminatedXKernel_solves parameters L compact state r
    simpa only [radialRetainedHighAKernel, fullKernelComposition_assoc,
      radialEliminatedXKernel_high_left] using equation
  rw [radialEliminatedSevenKernel, fullKernelComposition_add_inner, first,
    radialEliminationRightHandKernel_expansion]
  apply FullTwoFrequencyKernel.ext_entry
  intro shift mode
  simp only [fullKernelAdd_entry, fullKernelSub_entry]
  abel

def assembledNormalizedEightTrace (parameters : PhaseParameters) (angular cell : ℕ)
    (x : NegativeTrace parameters angular cell 1) (input : NegativeTrace parameters angular cell 8) :
    NegativeTrace parameters angular cell 7 :=
  fullNegativeKernelAction parameters angular cell (coordinateInjectionKernel parameters 7 0) x +
    fullNegativeKernelAction parameters angular cell (knownEightToSevenKernel parameters) input

theorem assembledNormalizedEightTrace_firstRow (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) (angular cell : ℕ)
    (x : NegativeTrace (radialKernelParameters parameters r) angular cell 1)
    (high : IsHighAngularTrace (radialKernelParameters parameters r) angular cell x)
    (input : NegativeTrace (radialKernelParameters parameters r) angular cell 8) :
    fullNegativeKernelAction (radialKernelParameters parameters r) angular cell
      (radialNormalizedRetainedFirstRowKernel parameters L compact state.val r)
      (assembledNormalizedEightTrace (radialKernelParameters parameters r) angular cell x input) =
      fullNegativeKernelAction (radialKernelParameters parameters r) angular cell
        (radialRetainedHighAKernel parameters L compact state.val r) x +
      fullNegativeKernelAction (radialKernelParameters parameters r) angular cell
        (fullKernelComposition (radialNormalizedRetainedFirstRowKernel parameters L compact state.val r)
          (knownEightToSevenKernel (radialKernelParameters parameters r))) input := by
  simp only [assembledNormalizedEightTrace, radialRetainedHighAKernel, map_add,
    fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply, highAngularKernel_fixed _ _ _ x high]

/-- No new data hypothesis: the independent eight inputs determine the unique high x. -/
theorem normalizedFirstRow_elimination_iff (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) (angular cell : ℕ)
    (x : NegativeTrace (radialKernelParameters parameters r) angular cell 1)
    (high : IsHighAngularTrace (radialKernelParameters parameters r) angular cell x)
    (input : NegativeTrace (radialKernelParameters parameters r) angular cell 8) :
    fullNegativeKernelAction (radialKernelParameters parameters r) angular cell
      (fullKernelComposition (highAngularKernel (radialKernelParameters parameters r) 1)
        (eightInputSlotKernel (radialKernelParameters parameters r) 0)) input =
      fullNegativeKernelAction (radialKernelParameters parameters r) angular cell
        (radialNormalizedRetainedFirstRowKernel parameters L compact state.val r)
        (assembledNormalizedEightTrace (radialKernelParameters parameters r) angular cell x input) +
      fullNegativeKernelAction (radialKernelParameters parameters r) angular cell
        (fullKernelComposition (highAngularKernel (radialKernelParameters parameters r) 1)
          (eightInputSlotKernel (radialKernelParameters parameters r) 7)) input ↔
    x = fullNegativeKernelAction (radialKernelParameters parameters r) angular cell
      (radialEliminatedXKernel parameters L compact state r) input := by
  rw [assembledNormalizedEightTrace_firstRow parameters L compact state r angular cell x high input]
  have rhs := congrArg
    (fun kernel => fullNegativeKernelAction (radialKernelParameters parameters r) angular cell kernel input)
    (radialEliminationRightHandKernel_expansion parameters L compact state r)
  simp only [fullNegativeKernelAction_sub] at rhs
  constructor
  · intro equation
    have isolated : fullNegativeKernelAction (radialKernelParameters parameters r) angular cell
        (radialRetainedHighAKernel parameters L compact state.val r) x =
      fullNegativeKernelAction (radialKernelParameters parameters r) angular cell
        (radialEliminationRightHandKernel parameters L compact state r) input := by
      rw [rhs, equation]
      abel
    have inverse := congrArg
      (fullNegativeKernelAction (radialKernelParameters parameters r) angular cell
        (radialRetainedHighInverse parameters L compact state r)) isolated
    change ((fullNegativeKernelAction (radialKernelParameters parameters r) angular cell
      (radialRetainedHighInverse parameters L compact state r)).comp
      (fullNegativeKernelAction (radialKernelParameters parameters r) angular cell
        (radialRetainedHighAKernel parameters L compact state.val r))) x = _ at inverse
    rw [← fullNegativeKernelAction_comp, radialRetainedHighInverse_left,
      highAngularKernel_fixed _ _ _ x high] at inverse
    simpa only [radialEliminatedXKernel, fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply] using inverse
  · intro equation
    rw [equation]
    have solved := congrArg
      (fun kernel => fullNegativeKernelAction (radialKernelParameters parameters r) angular cell kernel input)
      (radialEliminatedXKernel_solves parameters L compact state r)
    simp only [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply] at solved
    rw [solved, rhs]
    abel

end Grad.AnnularReconstruction
