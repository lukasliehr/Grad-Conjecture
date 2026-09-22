import AHX7RegularRadialActionAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularKernelL2
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.PhaseAlgebra Grad.BoundaryLift Grad.AnnularKernelContinuity Grad.ActualBoundaryPrimitives

variable (parameters : PhaseParameters) (power : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)

def highBulkProjection (dimension : ℕ) : DivisionRow dimension lower →L[ℂ] DivisionRow dimension lower :=
  regularRadialBulkAction parameters power lower positive bounded
    (fun r => highAngularKernel (radialKernelParameters parameters r) dimension)
    (scalarModeRadialKernel_regular parameters dimension highAngularMultiplier 1 highAngularMultiplier_norm_le)

theorem highBulkProjection_ae {dimension : ℕ} (field : DivisionRow dimension lower) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1), ∀ mode,
      highBulkProjection parameters power lower positive bounded dimension field mode x =
        highAngularMultiplier mode • field mode x := by
  unfold highBulkProjection regularRadialBulkAction highAngularKernel scalarModeDiagonalKernel
  apply completedBulkKernel_diagonal_ae

/-- The actual normalized retained A, completed using its already-proved
radial continuity and moments. -/
def retainedAAction (L compact : ℝ) (state : RetainedInverseState parameters L compact) :
    DivisionRow 1 lower →L[ℂ] DivisionRow 1 lower :=
  regularRadialBulkAction parameters power lower positive bounded
    (radialRetainedHighAKernel parameters L compact state.val)
    (radialRetainedHighAKernel_regular parameters L compact state.val)

/-- This is exactly the previously accepted retained inverse action; its
bounded construction is unchanged. -/
theorem retainedInverseAction_eq_regular (L compact : ℝ) (state : RetainedInverseState parameters L compact) :
    retainedInverseAction parameters L compact lower positive bounded state power =
      regularRadialBulkAction parameters power lower positive bounded
        (radialRetainedHighInverse parameters L compact state)
        (radialRetainedHighInverse_regular parameters L compact state) := by
  unfold retainedInverseAction retainedInverseFamily
  symm
  apply regularRadialBulkAction_eq_completed

theorem retainedCompletedInverse_left (L compact : ℝ) (state : RetainedInverseState parameters L compact) :
    (retainedInverseAction parameters L compact lower positive bounded state power).comp
      (retainedAAction parameters power lower positive bounded L compact state) =
      highBulkProjection parameters power lower positive bounded 1 := by
  rw [retainedInverseAction_eq_regular, retainedAAction, ← regularRadialBulkAction_comp]
  unfold highBulkProjection
  apply regularRadialBulkAction_congr
  exact radialRetainedHighInverse_left parameters L compact state

theorem retainedCompletedInverse_right (L compact : ℝ) (state : RetainedInverseState parameters L compact) :
    (retainedAAction parameters power lower positive bounded L compact state).comp
      (retainedInverseAction parameters L compact lower positive bounded state power) =
      highBulkProjection parameters power lower positive bounded 1 := by
  rw [retainedInverseAction_eq_regular, retainedAAction, ← regularRadialBulkAction_comp]
  unfold highBulkProjection
  apply regularRadialBulkAction_congr
  exact radialRetainedHighInverse_right parameters L compact state

theorem retainedInverseAction_high (L compact : ℝ) (state : RetainedInverseState parameters L compact)
    (field : DivisionRow 1 lower) (mode : ℤ × ℤ) (low : |mode.1| < 3) :
    retainedInverseAction parameters L compact lower positive bounded state power field mode = 0 := by
  unfold retainedInverseAction
  apply completedBulkKernel_high
  · intro x
    exact radialRetainedHighInverse_high_left parameters L compact state (collarRadius lower positive bounded x)
  · exact low

end Grad.AnnularKernelL2
