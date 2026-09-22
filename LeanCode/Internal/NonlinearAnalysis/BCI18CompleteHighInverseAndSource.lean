import BCI17LiteralBoundaryTupleBlocks

noncomputable section
set_option maxHeartbeats 1200000
namespace Grad.ActualBoundaryInverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.GaugeCoefficients.Physical.Allocation

theorem highAngularKernel_fixed {dimension : ℕ} (parameters : PhaseParameters) (angular cell : ℕ)
    (field : NegativeTrace parameters angular cell dimension) (high : IsHighAngularTrace parameters angular cell field) :
    fullNegativeKernelAction parameters angular cell (highAngularKernel parameters dimension) field = field := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  rw [highAngularKernel_coefficient]
  by_cases supported : 3 ≤ |mode.1|
  · simp only [highAngularMultiplier, if_pos supported, one_smul]
  · rw [high mode (lt_of_not_ge supported)]
    simp

theorem highKernelAction {input output : ℕ} (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FullTwoFrequencyKernel parameters input output)
    (supported : fullKernelComposition (highAngularKernel parameters output) kernel = kernel)
    (field : NegativeTrace parameters angular cell input) :
    IsHighAngularTrace parameters angular cell (fullNegativeKernelAction parameters angular cell kernel field) := by
  rw [← supported, fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
  exact highAngularKernel_high parameters angular cell _

variable {parameters : PhaseParameters} {L compact : ℝ}

theorem actualBoundaryT_high_left (state : PhysicalBoundaryState parameters L compact) :
    fullKernelComposition (highAngularKernel parameters 1) state.boundaryT = state.boundaryT := by
  rw [boundaryT_eq_high_negativeIdentity, ← fullKernelComposition_assoc, highAngularKernel_idempotent]

def actualBoundaryTOnHigh (state : PhysicalBoundaryState parameters L compact) (angular cell : ℕ) :
    HighBoundaryPrimitive parameters angular cell →L[ℂ] HighBoundaryPrimitive parameters angular cell :=
  ((fullNegativeKernelAction parameters angular cell state.boundaryT).comp
    (highAngularSubmodule parameters angular cell 1).subtypeL).codRestrict
    (highAngularSubmodule parameters angular cell 1)
    (fun field => highKernelAction parameters angular cell state.boundaryT (actualBoundaryT_high_left state) field.val)

def actualBoundaryInverseOnHigh (state : BoundaryInverseState parameters L compact) (angular cell : ℕ) :
    HighBoundaryPrimitive parameters angular cell →L[ℂ] HighBoundaryPrimitive parameters angular cell :=
  ((fullNegativeKernelAction parameters angular cell (actualHighBoundaryInverse state.val state.property)).comp
    (highAngularSubmodule parameters angular cell 1).subtypeL).codRestrict
    (highAngularSubmodule parameters angular cell 1)
    (fun field => highKernelAction parameters angular cell _ (actualHighBoundaryInverse_high_left state.val state.property) field.val)

theorem actualBoundaryInverseOnHigh_left (state : BoundaryInverseState parameters L compact) (angular cell : ℕ)
    (field : HighBoundaryPrimitive parameters angular cell) :
    actualBoundaryInverseOnHigh state angular cell (actualBoundaryTOnHigh state.val angular cell field) = field := by
  apply Subtype.ext
  change ((fullNegativeKernelAction parameters angular cell (actualHighBoundaryInverse state.val state.property)).comp
    (fullNegativeKernelAction parameters angular cell state.val.boundaryT)) field.val = field.val
  rw [← fullNegativeKernelAction_comp, actualHighBoundaryInverse_left]
  exact highAngularKernel_fixed parameters angular cell field.val field.property

theorem actualBoundaryInverseOnHigh_right (state : BoundaryInverseState parameters L compact) (angular cell : ℕ)
    (field : HighBoundaryPrimitive parameters angular cell) :
    actualBoundaryTOnHigh state.val angular cell (actualBoundaryInverseOnHigh state angular cell field) = field := by
  apply Subtype.ext
  change ((fullNegativeKernelAction parameters angular cell state.val.boundaryT).comp
    (fullNegativeKernelAction parameters angular cell (actualHighBoundaryInverse state.val state.property))) field.val = field.val
  rw [← fullNegativeKernelAction_comp, actualHighBoundaryInverse_right]
  exact highAngularKernel_fixed parameters angular cell field.val field.property

/-- AI10's actual isomorphism of the complete high negative-half carrier. -/
def actualBoundaryHighEquiv (state : BoundaryInverseState parameters L compact) (angular cell : ℕ) :
    HighBoundaryPrimitive parameters angular cell ≃L[ℂ] HighBoundaryPrimitive parameters angular cell where
  toLinearEquiv :=
    { (actualBoundaryTOnHigh state.val angular cell).toLinearMap with
      invFun := actualBoundaryInverseOnHigh state angular cell
      left_inv := actualBoundaryInverseOnHigh_left state angular cell
      right_inv := actualBoundaryInverseOnHigh_right state angular cell }
  continuous_toFun := (actualBoundaryTOnHigh state.val angular cell).continuous
  continuous_invFun := (actualBoundaryInverseOnHigh state angular cell).continuous

/-- The literal BS33 source contribution, with its required minus sign. -/
def actualSourceBoundaryLiftKernel (state : BoundaryInverseState parameters L compact) : FullTwoFrequencyKernel parameters 3 1 :=
  fullKernelNeg (fullKernelComposition (actualHighBoundaryInverse state.val state.property) (actualBoundaryH state.val))

/-- AI11's retained contribution -T^{-1}Nz. -/
def actualRetainedBoundaryLiftKernel (state : BoundaryInverseState parameters L compact) : FullTwoFrequencyKernel parameters 3 1 :=
  fullKernelNeg (fullKernelComposition (actualHighBoundaryInverse state.val state.property) (actualBoundaryN state.val))

theorem actualBoundaryH_high (state : PhysicalBoundaryState parameters L compact) :
    fullKernelComposition (highAngularKernel parameters 1) (actualBoundaryH state) = actualBoundaryH state := by
  unfold actualBoundaryH PhysicalBoundaryState.physicalRow actualDifferentiatedPhysicalBoundaryKernel
  rw [← fullKernelComposition_assoc, ← fullKernelComposition_assoc, highAngularKernel_idempotent]

theorem actualBoundaryN_high (state : PhysicalBoundaryState parameters L compact) :
    fullKernelComposition (highAngularKernel parameters 1) (actualBoundaryN state) = actualBoundaryN state := by
  unfold actualBoundaryN PhysicalBoundaryState.physicalRow actualDifferentiatedPhysicalBoundaryKernel
  rw [← fullKernelComposition_assoc, ← fullKernelComposition_assoc, highAngularKernel_idempotent]

theorem actualSourceBoundaryLift_equation (state : BoundaryInverseState parameters L compact) :
    fullKernelAdd (fullKernelComposition state.val.boundaryT (actualSourceBoundaryLiftKernel state)) (actualBoundaryH state.val) =
      fullZeroKernel parameters 3 1 := by
  unfold actualSourceBoundaryLiftKernel
  rw [fullKernelComposition_neg_inner, ← fullKernelComposition_assoc, actualHighBoundaryInverse_right, actualBoundaryH_high]
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  simp only [fullKernelAdd_entry, fullKernelNeg_entry, fullZeroKernel_entry]
  exact neg_add_cancel _

theorem actualSourceBoundaryLift_high (state : BoundaryInverseState parameters L compact) :
    fullKernelComposition (highAngularKernel parameters 1) (actualSourceBoundaryLiftKernel state) = actualSourceBoundaryLiftKernel state := by
  unfold actualSourceBoundaryLiftKernel
  rw [fullKernelComposition_neg_inner, ← fullKernelComposition_assoc, actualHighBoundaryInverse_high_left]

theorem actualSourceBoundaryLift_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    BoundaryInverseMoments parameters L compact actualSourceBoundaryLiftKernel :=
  UniformKernelMoments.neg (BoundaryInverseMoments.comp (actualHighBoundaryInverse_physicalMoments parameters L compact)
    (BoundaryInverseMoments.restrict (BoundaryDeviationMoments.regular (actualBoundaryH_vanishingMoments parameters L compact))))

end Grad.ActualBoundaryInverse
