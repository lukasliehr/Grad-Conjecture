import AKAG1CompactWeakSmoothTests
import T1Canonical

noncomputable section

set_option maxHeartbeats 300000

open MeasureTheory LineDeriv
open scoped ContDiff SchwartzMap

namespace Grad.CartesianStartup

open Grad.PDEBootstrap

/-- The accepted measure identification and its representative law are kept
 together, avoiding reduction of the measure-transport implementation. -/
def startupWholePlaneTransport :
    { equivalence : Grad.GenericCarriers.FieldL2 3 Set.univ ≃ₗᵢ[ℂ] FieldL2 //
      Grad.SpatialTranslation.PreservesRepresentatives CellValues equivalence } :=
  ⟨Grad.SpatialTranslation.canonicalToVolume CellValues,
    Grad.SpatialTranslation.canonicalToVolume_ae CellValues⟩

def startupWholePlaneField : Grad.GenericCarriers.FieldL2 3 Set.univ ≃ₗᵢ[ℂ] FieldL2 :=
  startupWholePlaneTransport.val

def startupRealSchwartz (test : 𝓢(Spatial, ℝ)) : 𝓢(Spatial, ℂ) :=
  test.postcompCLM Complex.ofRealCLM

theorem startupRealSchwartz_apply (test : 𝓢(Spatial, ℝ)) (point : Spatial) :
    startupRealSchwartz test point = (test point : ℂ) := rfl

theorem startupSchwartz_smul_integrable (field : FieldL2) (test : 𝓢(Spatial, ℂ)) :
    Integrable (fun point => test point • field point) volume := by
  have product : MemLp ((test : Spatial → ℂ) • (field : Spatial → CellValues)) 1 volume :=
    (Lp.memLp field).smul (test.memLp 2 volume)
  exact memLp_one_iff_integrable.mp product

theorem startupRealSchwartz_derivative (test : 𝓢(Spatial, ℝ)) (direction : Fin 2) :
    lineDerivOp (spatialDirection direction) (startupRealSchwartz test) =
      startupRealSchwartz (lineDerivOp (spatialDirection direction) test) := by
  apply SchwartzMap.ext
  intro point
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, startupRealSchwartz_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change fderiv ℝ (Complex.ofRealCLM ∘ (test : Spatial → ℝ)) point (spatialDirection direction) = _
  have differentiable : DifferentiableAt ℝ (test : Spatial → ℝ) point :=
    test.smooth'.differentiable (by simp) point
  have derivative := fderiv_comp point Complex.ofRealCLM.differentiableAt differentiable
  have applied := congrArg (fun derivative : Spatial →L[ℝ] ℂ => derivative (spatialDirection direction)) derivative
  rw [Complex.ofRealCLM.fderiv] at applied
  exact applied

theorem startupSchwartz_pairing
    (field : FieldL2) (test : 𝓢(Spatial, ℂ))
    (cell : ℤ) (vector : EuclideanSpace ℂ (Fin 3)) :
    inner ℂ vector ((distributionEmbedding field test) cell) =
      ∫ point, test point • inner ℂ vector (field point cell) := by
  let functional : CellValues →L[ℂ] ℂ :=
    (innerSL ℂ vector).comp (lp.evalCLM ℂ (fun _ : ℤ => EuclideanSpace ℂ (Fin 3)) 2 cell)
  change functional (distributionEmbedding field test) = _
  calc
    functional (distributionEmbedding field test) =
        functional (∫ point, test point • field point) :=
      congrArg functional (Lp.toTemperedDistribution_apply field test)
    _ = ∫ point, functional (test point • field point) :=
      (functional.integral_comp_comm (startupSchwartz_smul_integrable field test)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with point
      exact functional.map_smul (test point) (field point)

theorem startupRepresentedEquivalence_ae
    (equivalence : Grad.GenericCarriers.FieldL2 3 Set.univ ≃ₗᵢ[ℂ] FieldL2)
    (represented : Grad.SpatialTranslation.PreservesRepresentatives CellValues equivalence)
    (field : Grad.GenericCarriers.FieldL2 3 Set.univ) :
    (equivalence field : Spatial → CellValues) =ᵐ[volume] field := by
  exact represented field

theorem startupWholePlaneField_ae
    (field : Grad.GenericCarriers.FieldL2 3 Set.univ) :
    (startupWholePlaneField field : Spatial → CellValues) =ᵐ[volume] field :=
  startupRepresentedEquivalence_ae startupWholePlaneField startupWholePlaneTransport.property field

theorem startupRealSchwartz_pairing
    (field : Grad.GenericCarriers.FieldL2 3 Set.univ) (test : 𝓢(Spatial, ℝ))
    (cell : ℤ) (vector : EuclideanSpace ℂ (Fin 3)) :
    inner ℂ vector ((distributionEmbedding (startupWholePlaneField field) (startupRealSchwartz test)) cell) =
      ∫ point in (Set.univ : Set Spatial), test point • inner ℂ vector (field point cell) := by
  rw [startupSchwartz_pairing, setIntegral_univ]
  apply integral_congr_ae
  filter_upwards [startupWholePlaneField_ae field] with point represented
  rw [represented, startupRealSchwartz_apply]
  exact Complex.coe_smul (test point) (inner ℂ vector (field point cell))

end Grad.CartesianStartup
