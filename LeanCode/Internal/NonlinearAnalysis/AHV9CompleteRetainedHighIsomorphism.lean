import AHV8RetainedInversePhysicalMoments

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse
variable {parameters : PhaseParameters} {L compact : ℝ}

def radialRetainedAOnHigh (state : RetainedInverseState parameters L compact) (r : RadialPoint) (angular cell : ℕ) :
    HighBoundaryPrimitive (radialKernelParameters parameters r) angular cell →L[ℂ] HighBoundaryPrimitive (radialKernelParameters parameters r) angular cell :=
  ((fullNegativeKernelAction (radialKernelParameters parameters r) angular cell (radialRetainedHighAKernel parameters L compact state.val r)).comp
    (highAngularSubmodule (radialKernelParameters parameters r) angular cell 1).subtypeL).codRestrict
    (highAngularSubmodule (radialKernelParameters parameters r) angular cell 1)
    (fun field => highKernelAction (radialKernelParameters parameters r) angular cell (radialRetainedHighAKernel parameters L compact state.val r) (radialRetainedHighAKernel_high_left parameters L compact state.val r) field.val)

def radialRetainedInverseOnHigh (state : RetainedInverseState parameters L compact) (r : RadialPoint) (angular cell : ℕ) :
    HighBoundaryPrimitive (radialKernelParameters parameters r) angular cell →L[ℂ] HighBoundaryPrimitive (radialKernelParameters parameters r) angular cell :=
  ((fullNegativeKernelAction (radialKernelParameters parameters r) angular cell (radialRetainedHighInverse parameters L compact state r)).comp
    (highAngularSubmodule (radialKernelParameters parameters r) angular cell 1).subtypeL).codRestrict
    (highAngularSubmodule (radialKernelParameters parameters r) angular cell 1)
    (fun field => highKernelAction (radialKernelParameters parameters r) angular cell _ (radialRetainedHighInverse_high_left parameters L compact state r) field.val)

theorem radialRetainedInverseOnHigh_left (state : RetainedInverseState parameters L compact) (r : RadialPoint) (angular cell : ℕ)
    (field : HighBoundaryPrimitive (radialKernelParameters parameters r) angular cell) :
    radialRetainedInverseOnHigh state r angular cell (radialRetainedAOnHigh state r angular cell field) = field := by
  apply Subtype.ext
  change ((fullNegativeKernelAction (radialKernelParameters parameters r) angular cell (radialRetainedHighInverse parameters L compact state r)).comp
    (fullNegativeKernelAction (radialKernelParameters parameters r) angular cell (radialRetainedHighAKernel parameters L compact state.val r))) field.val = field.val
  rw [← fullNegativeKernelAction_comp, radialRetainedHighInverse_left]
  exact highAngularKernel_fixed (radialKernelParameters parameters r) angular cell field.val field.property

theorem radialRetainedInverseOnHigh_right (state : RetainedInverseState parameters L compact) (r : RadialPoint) (angular cell : ℕ)
    (field : HighBoundaryPrimitive (radialKernelParameters parameters r) angular cell) :
    radialRetainedAOnHigh state r angular cell (radialRetainedInverseOnHigh state r angular cell field) = field := by
  apply Subtype.ext
  change ((fullNegativeKernelAction (radialKernelParameters parameters r) angular cell (radialRetainedHighAKernel parameters L compact state.val r)).comp
    (fullNegativeKernelAction (radialKernelParameters parameters r) angular cell (radialRetainedHighInverse parameters L compact state r))) field.val = field.val
  rw [← fullNegativeKernelAction_comp, radialRetainedHighInverse_right]
  exact highAngularKernel_fixed (radialKernelParameters parameters r) angular cell field.val field.property

/-- The actual retained A isomorphism on the complete high negative-half carrier at every radius. -/
def radialRetainedHighEquiv (state : RetainedInverseState parameters L compact) (r : RadialPoint) (angular cell : ℕ) :
    HighBoundaryPrimitive (radialKernelParameters parameters r) angular cell ≃L[ℂ] HighBoundaryPrimitive (radialKernelParameters parameters r) angular cell where
  toLinearEquiv :=
    { (radialRetainedAOnHigh state r angular cell).toLinearMap with
      invFun := radialRetainedInverseOnHigh state r angular cell
      left_inv := radialRetainedInverseOnHigh_left state r angular cell
      right_inv := radialRetainedInverseOnHigh_right state r angular cell }
  continuous_toFun := (radialRetainedAOnHigh state r angular cell).continuous
  continuous_invFun := (radialRetainedInverseOnHigh state r angular cell).continuous


/-- Exact solution equivalence for the retained equation on the complete carrier. -/
theorem radialRetainedA_equation_iff (state : RetainedInverseState parameters L compact)
    (r : RadialPoint) (angular cell : ℕ)
    (x datum : HighBoundaryPrimitive (radialKernelParameters parameters r) angular cell) :
    radialRetainedAOnHigh state r angular cell x = datum ↔
      x = radialRetainedInverseOnHigh state r angular cell datum := by
  constructor
  · intro equation
    rw [← equation, radialRetainedInverseOnHigh_left]
  · intro equation
    rw [equation, radialRetainedInverseOnHigh_right]

/-- The original AHS retained A, restricted to actual high inputs, has this same inverse. -/
theorem originalRetainedA_equation_iff (state : RetainedInverseState parameters L compact)
    (r : RadialPoint) (positive : 0 < r.val) (angular cell : ℕ)
    (x datum : HighBoundaryPrimitive (radialKernelParameters parameters r) angular cell) :
    fullNegativeKernelAction (radialKernelParameters parameters r) angular cell
      (radialRetainedAKernel parameters L compact state.val.val r state.val.property positive) x.val = datum.val ↔
      x = radialRetainedInverseOnHigh state r angular cell datum := by
  have same : fullNegativeKernelAction (radialKernelParameters parameters r) angular cell
      (radialRetainedAKernel parameters L compact state.val.val r state.val.property positive) x.val =
      (radialRetainedAOnHigh state r angular cell x).val := by
    change _ = fullNegativeKernelAction (radialKernelParameters parameters r) angular cell
      (radialRetainedHighAKernel parameters L compact state.val r) x.val
    rw [← radialRetainedHighAKernel_original parameters L compact state.val r positive,
      fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
      highAngularKernel_fixed (radialKernelParameters parameters r) angular cell x.val x.property]
  rw [same, Subtype.val_inj]
  exact radialRetainedA_equation_iff state r angular cell x datum

end Grad.AnnularReconstruction
