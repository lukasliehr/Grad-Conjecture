import AID13LiteralPhysicalOuterTesting

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set MeasureTheory Filter
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularCurrentGreen
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularCircularForm
open Grad.AnnularTiltedReference Grad.AnnularGrades Grad.CircularHighRegularity Grad.AnnularSourceGraph
open Grad.AnnularConverse Grad.AnnularCurrentBoundary Grad.AnnularUniformBoundary Grad.BoundaryKernelAction

/-- The accepted actual zero-core density extends complex linear test functionals. -/
theorem actualComplexTestFunctional_vanish (lower L : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < L)
    (functional : annularEnergySpace lower L positive →L[ℂ] ℂ)
    (single : ∀ (mode : HighAnnularMode) (core : complexSmoothRadialCore 1), core.val.1 lower = 0 →
      functional (annularEnergyCoreInto lower L positive (Finsupp.single mode core)) = 0)
    (test : annularInnerZero lower L positive bounded lengthPositive) : functional test.val = 0 := by
  classical
  apply isClosed_property (annularZeroSmoothInto_denseRange lower L positive bounded lengthPositive)
    (isClosed_eq (functional.continuous.comp continuous_subtype_val) continuous_const) _ test
  intro core
  change functional (annularEnergyCoreInto lower L positive core.val) = 0
  have decomposition : core.val = ∑ mode ∈ core.val.support, Finsupp.single mode (core.val mode) :=
    (Finsupp.sum_single core.val).symm
  rw [decomposition, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro mode _
  exact single mode (core.val mode) ((annularZeroSmoothCore_iff lower core.val).mp core.property mode)

theorem bEnergyDecode_inner_zero (lower L : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (lengthPositive : 0 < L) (test : annularEnergySpace lower L positive)
    (zero : annularEnergyTrace lower L positive bounded lengthPositive 0 test = 0) :
    annularEnergyTrace lower L positive bounded lengthPositive 0 (bEnergyDecode lower L positive test) = 0 := by
  rw [bEnergyDecode, annularEnergyTrace_diagonal, zero, map_zero]

variable (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))

def physicalPacketResidual (field : DivisionRow 3 lower) (boundary : NegativeTrace parameters 0 0 1) :
    annularEnergySpace lower L positive →L[ℂ] ℂ :=
  (innerSL ℂ field).comp
    ((highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength).comp (bEnergyNormalize lower L positive)) -
  (innerSL ℂ boundary).comp
    ((actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0).comp (bEnergyNormalize lower L positive))

theorem physicalPacketResidual_literal (field : DivisionRow 3 lower) (boundary : NegativeTrace parameters 0 0 1)
    (test : annularEnergySpace lower L positive) :
    physicalPacketResidual parameters lower L positive lowerHalf lengthPositive widthHalf widthLength field boundary test =
      starRingEnd ℂ (inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength
        (bEnergyNormalize lower L positive test)) field -
        inner ℂ (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0
          (bEnergyNormalize lower L positive test)) boundary) := by
  change inner ℂ field (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength
      (bEnergyNormalize lower L positive test)) -
    inner ℂ boundary (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0
      (bEnergyNormalize lower L positive test)) = _
  rw [map_sub, inner_conj_symm, inner_conj_symm]

/-- The actual compact radial equation and genuine moment endpoint recover the completed variational packet law. -/
theorem physicalFlux_packet_converse (field : DivisionRow 3 lower) (boundary : NegativeTrace parameters 0 0 1)
    (equation : CompactPhysicalPacketEquation parameters lower L positive lengthPositive widthHalf widthLength field)
    (outer : ∀ mode : HighAnnularMode,
      weightedRadialTrace 1 lower positive (lowerHalf.trans_lt (by norm_num)) 1
        (physicalFluxMomentGraph parameters lower L positive lengthPositive widthHalf widthLength
          (lowerHalf.trans_lt (by norm_num)) field equation mode) =
        (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) • boundary mode.val)
    (test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive) :
    inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test.val) field =
      inner ℂ (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test.val) boundary := by
  let residual := physicalPacketResidual parameters lower L positive lowerHalf lengthPositive widthHalf widthLength field boundary
  have single (mode : HighAnnularMode) (core : complexSmoothRadialCore 1) (zero : core.val.1 lower = 0) :
      residual (annularEnergyCoreInto lower L positive (Finsupp.single mode core)) = 0 := by
    rw [show residual = physicalPacketResidual parameters lower L positive lowerHalf lengthPositive widthHalf widthLength field boundary from rfl,
      physicalPacketResidual_literal, physicalFlux_packet_green parameters lower L positive lengthPositive widthHalf widthLength
        (lowerHalf.trans_lt (by norm_num)) field equation mode, physicalOuterTest_single,
      zero, inner_zero_left, sub_zero, outer mode, sub_self, map_zero]
  let decoded : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive :=
    ⟨bEnergyDecode lower L positive test.val,
      bEnergyDecode_inner_zero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive test.val test.property⟩
  have zero := actualComplexTestFunctional_vanish lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive residual single decoded
  change physicalPacketResidual parameters lower L positive lowerHalf lengthPositive widthHalf widthLength field boundary
    (bEnergyDecode lower L positive test.val) = 0 at zero
  rw [physicalPacketResidual_literal, bEnergyNormalize_decode] at zero
  have twice := congrArg (starRingEnd ℂ) zero
  have difference : inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test.val) field -
      inner ℂ (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test.val) boundary = 0 := by
    simpa using twice
  exact sub_eq_zero.mp difference

end Grad.AnnularCurrentGreen
