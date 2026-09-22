import AJD28ActualCoefficientCoordinateBounds
import AJD30UniformOperatorOperations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularCrossMaps Grad.AnnularKernelOrbit Grad.AnnularCurrentEnergy
open Grad.AnnularCurrentBoundary Grad.AnnularUniformBoundary Grad.AnnularReconstruction Grad.AnnularKernelL2
open Grad.ActualBoundaryPrimitives

attribute [local instance] crossDataNormed crossDataSeminormed crossDataRealInner crossDataRealNormed crossDataRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule

variable (parameters : PhaseParameters) (lower : ℝ)

theorem crossBulkCoordinate_bound (row : Fin 3) (datum : CrossHighData parameters lower) :
    ‖crossBulkCoordinate parameters lower row datum‖ ≤ ‖datum‖ := by
  change ‖datum.ofLp.1 row‖ ≤ ‖datum‖
  have pair := WithLp.prod_norm_sq_eq_of_L2 datum
  have bulk := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => AnnularBulk lower) datum.ofLp.1
  have single : ‖datum.ofLp.1 row‖ ^ 2 ≤ ∑ index : Fin 3, ‖datum.ofLp.1 index‖ ^ 2 :=
    Finset.single_le_sum (f := fun index : Fin 3 => ‖datum.ofLp.1 index‖ ^ 2)
      (fun index _ => sq_nonneg ‖datum.ofLp.1 index‖) (Finset.mem_univ row)
  change ‖datum‖ ^ 2 = ‖datum.ofLp.1‖ ^ 2 + ‖datum.ofLp.2‖ ^ 2 at pair
  nlinarith [norm_nonneg (datum.ofLp.1 row), norm_nonneg datum, sq_nonneg ‖datum.ofLp.2‖]

theorem crossBoundaryCoordinate_norm : ‖crossBoundaryCoordinate parameters lower‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro datum
  change ‖datum.ofLp.2‖ ≤ 1 * ‖datum‖
  rw [one_mul]
  have pair := WithLp.prod_norm_sq_eq_of_L2 datum
  change ‖datum‖ ^ 2 = ‖datum.ofLp.1‖ ^ 2 + ‖datum.ofLp.2‖ ^ 2 at pair
  nlinarith [norm_nonneg datum.ofLp.2, norm_nonneg datum, sq_nonneg ‖datum.ofLp.1‖]

theorem crossKnownEight_norm : ‖crossKnownEight parameters lower‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro datum
  exact (highBulkSlot_bound lower (7 : Fin 8) _).trans
    ((crossBulkCoordinate_bound parameters lower 0 datum).trans_eq (one_mul _).symm)

theorem crossKnownDirect_norm : ‖crossKnownDirect parameters lower‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro datum
  have first := (highBulkSlot_bound lower (1 : Fin 3) _).trans (crossBulkCoordinate_bound parameters lower 1 datum)
  have second := (highBulkSlot_bound lower (2 : Fin 3) _).trans (crossBulkCoordinate_bound parameters lower 2 datum)
  exact (norm_add_le _ _).trans ((add_le_add first second).trans_eq (by ring))

theorem highEnergyTestPacket_norm (L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) :
    ‖highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength‖ ≤ 5 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (highEnergyTestPacket_bound parameters lower L positive lengthPositive widthHalf widthLength)

theorem actualCurrentHighOuterTrace_norm (L : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) :
    ‖actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0‖ ≤ uniformOuterTraceConstant L :=
  ContinuousLinearMap.opNorm_le_bound _ (uniformOuterTraceConstant_nonnegative L)
    (actualCurrentHighOuterTrace_bound parameters lower L positive lowerHalf lengthPositive 0 0)

section Restriction
variable {X W V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem operatorTestRestriction_bound (inclusion : V →L[ℝ] W) (mapping : X →L[ℝ] W →L[ℝ] ℝ) :
    ‖operatorTestRestriction (X := X) inclusion mapping‖ ≤ ‖inclusion‖ * ‖mapping‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro datum
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro field
  change ‖mapping datum (inclusion field)‖ ≤ _
  have actual := ((mapping datum).le_opNorm (inclusion field)).trans
    (mul_le_mul (mapping.le_opNorm datum) (inclusion.le_opNorm field) (norm_nonneg _)
      (mul_nonneg (norm_nonneg mapping) (norm_nonneg datum)))
  exact actual.trans_eq (by ring)
end Restriction
end Grad.AnnularCrossOrbit
