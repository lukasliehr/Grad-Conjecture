import AHT6LiteralPhysicalKernelAction

noncomputable section
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularKernelL2
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.PhaseAlgebra Grad.BoundaryLift Grad.AnnularKernelContinuity

/-- A continuous representative extension used only outside the physical
collar. On the collar this is exactly the original radius. -/
def collarRadius (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (x : ℝ) : RadialPoint :=
  ⟨max lower (min x 1), positive.le.trans (le_max_left _ _),
    max_le bounded (min_le_right _ _)⟩

theorem collarRadius_continuous (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) :
    Continuous (collarRadius lower positive bounded) :=
  (continuous_const.max (continuous_id.min continuous_const)).subtype_mk _

theorem collarRadius_lower (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (x : ℝ) :
    lower ≤ (collarRadius lower positive bounded x).val := le_max_left _ _

theorem collarRadius_literal (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (x : ℝ) (inside : x ∈ Icc lower 1) : (collarRadius lower positive bounded x).val = x := by
  change max lower (min x 1) = x
  rw [min_eq_left inside.2, max_eq_right inside.1]

def positiveCollarRadius (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (x : ℝ) : PositiveRadialPoint :=
  ⟨collarRadius lower positive bounded x, positive.trans_le (collarRadius_lower lower positive bounded x)⟩

theorem positiveCollarRadius_continuous (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) :
    Continuous (positiveCollarRadius lower positive bounded) :=
  (collarRadius_continuous lower positive bounded).subtype_mk _

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters L compact)

def originalCovariantFamily (x : ℝ) : RadialKernel parameters (collarRadius lower positive bounded x) 7 3 :=
  radialCovariantKernel parameters L compact state.val (collarRadius lower positive bounded x)
    state.property (positive.trans_le (collarRadius_lower lower positive bounded x))

def originalRotatedFamily (x : ℝ) : RadialKernel parameters (collarRadius lower positive bounded x) 7 3 :=
  radialRotatedCovariantKernel parameters L compact state.val (collarRadius lower positive bounded x)
    state.property (positive.trans_le (collarRadius_lower lower positive bounded x))

theorem originalCovariantFamily_measurable (shift mode : ℤ × ℤ) :
    AEStronglyMeasurable (fun x => (originalCovariantFamily parameters L compact lower positive bounded state x).entry shift mode)
      (volume.restrict (Icc lower 1)) :=
  ((radialCovariantKernel_continuous parameters L compact state shift mode).comp
    (positiveCollarRadius_continuous lower positive bounded)).aestronglyMeasurable

theorem originalRotatedFamily_measurable (shift mode : ℤ × ℤ) :
    AEStronglyMeasurable (fun x => (originalRotatedFamily parameters L compact lower positive bounded state x).entry shift mode)
      (volume.restrict (Icc lower 1)) :=
  ((radialRotatedCovariantKernel_continuous parameters L compact state shift mode).comp
    (positiveCollarRadius_continuous lower positive bounded)).aestronglyMeasurable

def originalKernelConstant (power : ℕ) : ℝ :=
  Classical.choose (originalSevenSlotKernel_oneHigh parameters L compact lower positive power)

theorem originalKernelConstant_nonnegative (power : ℕ) :
    0 ≤ originalKernelConstant parameters L compact lower positive power :=
  (Classical.choose_spec (originalSevenSlotKernel_oneHigh parameters L compact lower positive power)).1

theorem originalKernelConstant_bounds (power : ℕ) (x : ℝ) :
    fullKernelMoment (radialKernelParameters parameters (collarRadius lower positive bounded x)) power
      (originalCovariantFamily parameters L compact lower positive bounded state x) +
    fullKernelMoment (radialKernelParameters parameters (collarRadius lower positive bounded x)) power
      (originalRotatedFamily parameters L compact lower positive bounded state x) ≤
        originalKernelConstant parameters L compact lower positive power * state.val.size power :=
  (Classical.choose_spec (originalSevenSlotKernel_oneHigh parameters L compact lower positive power)).2
    state (collarRadius lower positive bounded x) (collarRadius_lower lower positive bounded x)

theorem originalCovariantFamily_moment (power : ℕ) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1),
    fullKernelMoment (radialKernelParameters parameters (collarRadius lower positive bounded x)) power
      (originalCovariantFamily parameters L compact lower positive bounded state x) ≤
        originalKernelConstant parameters L compact lower positive power * state.val.size power := by
  filter_upwards with x
  exact (le_add_of_nonneg_right (fullKernelMoment_nonnegative _ _ _)).trans
    (originalKernelConstant_bounds parameters L compact lower positive bounded state power x)

theorem originalRotatedFamily_moment (power : ℕ) :
    ∀ᵐ x ∂volume.restrict (Icc lower 1),
    fullKernelMoment (radialKernelParameters parameters (collarRadius lower positive bounded x)) power
      (originalRotatedFamily parameters L compact lower positive bounded state x) ≤
        originalKernelConstant parameters L compact lower positive power * state.val.size power := by
  filter_upwards with x
  exact (le_add_of_nonneg_left (fullKernelMoment_nonnegative _ _ _)).trans
    (originalKernelConstant_bounds parameters L compact lower positive bounded state power x)

end Grad.AnnularKernelL2
