import AHQ13ActualMassKernelContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.AnnularKernelContinuity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularReconstruction

/-- A constant-in-frequency input map collapses the actual convolution to
its zero shift. Its matrix may still vary with the physical radius. -/
theorem fullKernelComposition_constant_input_entry (parameters : PhaseParameters)
    {src mid tgt : ℕ} (outer : FullTwoFrequencyKernel parameters mid tgt)
    (mapping : ComplexEuclidean src →L[ℂ] ComplexEuclidean mid) (shift input : ℤ × ℤ) :
    (fullKernelComposition outer (constantMatrixKernel parameters src mid mapping)).entry shift input =
      (outer.entry shift input).comp mapping := by
  rw [fullKernelComposition_entry, tsum_eq_single (0, 0) (by
    intro middle nonzero
    rw [constantMatrixKernel_entry]
    simp only [if_neg nonzero, ContinuousLinearMap.comp_zero])]
  rw [constantMatrixKernel_entry]
  rw [show shift - (0, 0) = shift from sub_zero shift,
    show input + (0, 0) = input from add_zero input]
  rfl

abbrev PositiveRadialPoint := {r : RadialPoint // 0 < r.val}

theorem radialSevenSlotNormalization_continuous :
    Continuous (fun r : PositiveRadialPoint => radialSevenSlotNormalization r.val.val) := by
  have realRadius : Continuous (fun r : PositiveRadialPoint => r.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  have complexRadius : Continuous (fun r : PositiveRadialPoint => (r.val.val : ℂ)) :=
    Complex.continuous_ofReal.comp realRadius
  have reciprocal : Continuous (fun r : PositiveRadialPoint => (r.val.val : ℂ)⁻¹) :=
    complexRadius.inv₀ (fun r => Complex.ofReal_ne_zero.mpr (ne_of_gt r.property))
  unfold radialSevenSlotNormalization
  exact (((((continuous_const.add (reciprocal.smul continuous_const)).add continuous_const).add
    (reciprocal.smul continuous_const)).add continuous_const).add continuous_const).add continuous_const

variable (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact)

/-- Continuity of the literal original AH20 map, retaining 1/r in slots
one and three, on all positive radii including the outer endpoint. -/
theorem radialCovariantKernel_continuous (shift input : ℤ × ℤ) :
    Continuous (fun r : PositiveRadialPoint =>
      (radialCovariantKernel parameters L compact state.val r.val state.property r.property).entry shift input) := by
  have normalized : Continuous (fun r : PositiveRadialPoint =>
      (radialNormalizedCovariantKernel parameters L compact state.val r.val state.property).entry shift input) :=
    ((radialNormalizedCovariantKernel_regular parameters L compact state).1 shift input).comp
      (continuous_subtype_val : Continuous (fun r : PositiveRadialPoint => r.val))
  have composed := normalized.clm_comp radialSevenSlotNormalization_continuous
  simpa only [radialCovariantKernel, radialSevenSlotKernel,
    fullKernelComposition_constant_input_entry] using composed

theorem radialRotatedCovariantKernel_continuous (shift input : ℤ × ℤ) :
    Continuous (fun r : PositiveRadialPoint =>
      (radialRotatedCovariantKernel parameters L compact state.val r.val state.property r.property).entry shift input) := by
  have normalized : Continuous (fun r : PositiveRadialPoint =>
      (radialNormalizedRotatedCovariantKernel parameters L compact state.val r.val state.property).entry shift input) :=
    ((radialNormalizedRotatedCovariantKernel_regular parameters L compact state).1 shift input).comp
      (continuous_subtype_val : Continuous (fun r : PositiveRadialPoint => r.val))
  have composed := normalized.clm_comp radialSevenSlotNormalization_continuous
  simpa only [radialRotatedCovariantKernel, radialSevenSlotKernel,
    fullKernelComposition_constant_input_entry] using composed

end Grad.AnnularKernelContinuity
