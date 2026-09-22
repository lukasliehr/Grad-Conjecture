import AJE16FullKnownFunctionalTower

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularReconstruction
open Grad.AnnularHighInverseOrbit Grad.AnnularCrossOrbit Grad.AnnularKernelL2 Grad.AnnularCurrentEnergy
open Grad.AnnularCurrentBoundary Grad.AnnularUniformBoundary
attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule

section Pairing
variable {X V D : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup D] [InnerProductSpace ℂ D]
local instance sharedBoundRealInner : InnerProductSpace ℝ D := InnerProductSpace.rclikeToReal ℂ D

theorem pairedRealOperator_bound (test : V →L[ℝ] D) (mapping : X →L[ℝ] D) :
    ‖pairedRealOperator test mapping‖ ≤ ‖test‖ * ‖mapping‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg test) (norm_nonneg mapping))
  intro source
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg (norm_nonneg test) (norm_nonneg mapping)) (norm_nonneg source))
  intro field
  rw [pairedRealOperator_apply,Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm (𝕜 := ℂ) _ _).trans
    ((mul_le_mul (test.le_opNorm field) (mapping.le_opNorm source) (norm_nonneg _)
      (mul_nonneg (norm_nonneg test) (norm_nonneg field))).trans_eq (by ring)))
end Pairing

private theorem hilbertComponentBounds {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (data : WithLp 2 (E × F)) : ‖data.ofLp.1‖ ≤ ‖data‖ ∧ ‖data.ofLp.2‖ ≤ ‖data‖ :=
  ⟨hilbert_first_bound data,hilbert_second_bound data⟩

variable (parameters : PhaseParameters) (lower : ℝ)

theorem knownAmbientWeighted_bound (data : ActualHighKnownAmbient parameters lower 0 0) :
    ‖highKnownWeightedProjection parameters lower 0 0 data‖ ≤ ‖data‖ :=
  (hilbertComponentBounds data.ofLp.1).1.trans (hilbertComponentBounds data).1

theorem knownAmbientAuxiliary_bound (data : ActualHighKnownAmbient parameters lower 0 0) :
    ‖highKnownAuxiliaryProjection parameters lower 0 0 data‖ ≤ ‖data‖ :=
  (hilbertComponentBounds data.ofLp.1).2.trans (hilbertComponentBounds data).1

theorem knownAmbientGraphs_bound (data : ActualHighKnownAmbient parameters lower 0 0) :
    ‖knownAmbientGraphs parameters lower 0 0 data‖ ≤ ‖data‖ :=
  (hilbertComponentBounds data.ofLp.2).1.trans (hilbertComponentBounds data).2

theorem knownAmbientDatum_bound (data : ActualHighKnownAmbient parameters lower 0 0) :
    ‖highKnownDatumProjection parameters lower 0 0 data‖ ≤ ‖data‖ :=
  (hilbertComponentBounds data.ofLp.2.ofLp.2).1.trans
    ((hilbertComponentBounds data.ofLp.2).2.trans (hilbertComponentBounds data).2)

theorem knownAmbientEight_norm : ‖knownAmbientEight parameters lower 0 0‖ ≤ 4 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro data
  exact (highKnownEightPacket_bound lower data.ofLp.1.ofLp.1).trans
    (mul_le_mul_of_nonneg_left (knownAmbientWeighted_bound parameters lower data) (by norm_num))

theorem knownAmbientDirect_norm (positive : 0 < lower) :
    ‖knownAmbientDirect parameters lower 0 0 positive‖ ≤ 3 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro data
  exact (directKnownThreePacket_bound lower positive data.ofLp.1.ofLp.2).trans
    (mul_le_mul_of_nonneg_left (knownAmbientAuxiliary_bound parameters lower data) (by norm_num))

theorem knownAmbientDatum_norm : ‖highKnownDatumProjection parameters lower 0 0‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro data
  simpa only [one_mul] using knownAmbientDatum_bound parameters lower data

theorem knownAmbientSourceTuple_norm (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) :
    ‖knownAmbientSourceTuple parameters lower 0 0 positive (lowerHalf.trans_lt (by norm_num))‖ ≤
      3 * uniformSourceOuterConstant := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) uniformSourceOuterConstant_nonnegative)
  intro data
  exact (highGraphOuterTupleMap_uniform_bound parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 lowerHalf
    (knownAmbientGraphs parameters lower 0 0 data)).trans
      (mul_le_mul_of_nonneg_left (knownAmbientGraphs_bound parameters lower data)
        (mul_nonneg (by norm_num) uniformSourceOuterConstant_nonnegative))

variable (length : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (lengthPositive : 0 < length) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem knownEnergyTest_norm :
    ‖(highEnergyTestPacket parameters lower length positive lengthPositive widthHalf widthLength).restrictScalars ℝ‖ ≤ 5 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  exact highEnergyTestPacket_bound parameters lower length positive lengthPositive widthHalf widthLength

theorem knownOuterTest_norm :
    ‖(actualCurrentHighOuterTrace parameters lower length positive lowerHalf lengthPositive 0 0).restrictScalars ℝ‖ ≤
      uniformOuterTraceConstant length := by
  apply ContinuousLinearMap.opNorm_le_bound _ (uniformOuterTraceConstant_nonnegative length)
  exact actualCurrentHighOuterTrace_bound parameters lower length positive lowerHalf lengthPositive 0 0

end Grad.AnnularStrongOrbit
