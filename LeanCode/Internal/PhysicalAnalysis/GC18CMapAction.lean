import GC18CMapAngular
import GC18APL2Action

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra

def cMapActionLinear {input output : ℕ} (coefficient : C(ClosedDisk, OperatorValue input output)) :
    C(ClosedDisk, ComplexEuclidean input) →ₗ[ℂ] C(ClosedDisk, ComplexEuclidean output) where
  toFun field := ⟨fun point => coefficient point (field point), coefficient.continuous.clm_apply field.continuous⟩
  map_add' first second := by
    apply ContinuousMap.ext
    intro point
    exact (coefficient point).map_add (first point) (second point)
  map_smul' scalar field := by
    apply ContinuousMap.ext
    intro point
    exact (coefficient point).map_smul scalar (field point)

theorem cMapAction_bound {input output : ℕ} (coefficient : C(ClosedDisk, OperatorValue input output))
    (field : C(ClosedDisk, ComplexEuclidean input)) :
    ‖cMapActionLinear coefficient field‖ ≤ ‖coefficient‖ * ‖field‖ := by
  apply (ContinuousMap.norm_le (cMapActionLinear coefficient field)
    (mul_nonneg (norm_nonneg coefficient) (norm_nonneg field))).mpr
  intro point
  exact ((coefficient point).le_opNorm (field point)).trans
    (mul_le_mul (ContinuousMap.norm_coe_le_norm coefficient point) (ContinuousMap.norm_coe_le_norm field point)
      (norm_nonneg (field point)) (norm_nonneg coefficient))

def cMapAction {input output : ℕ} (coefficient : C(ClosedDisk, OperatorValue input output)) :
    C(ClosedDisk, ComplexEuclidean input) →L[ℂ] C(ClosedDisk, ComplexEuclidean output) :=
  (cMapActionLinear coefficient).mkContinuous ‖coefficient‖ (cMapAction_bound coefficient)

theorem cMapAction_norm_le {input output : ℕ} (coefficient : C(ClosedDisk, OperatorValue input output)) :
    ‖cMapAction coefficient‖ ≤ ‖coefficient‖ :=
  LinearMap.mkContinuous_norm_le (cMapActionLinear coefficient) (norm_nonneg coefficient) (cMapAction_bound coefficient)

def cMapActionBilinear (input output : ℕ) :
    C(ClosedDisk, OperatorValue input output) →L[ℂ]
      C(ClosedDisk, ComplexEuclidean input) →L[ℂ] C(ClosedDisk, ComplexEuclidean output) := by
  let mapping : C(ClosedDisk, OperatorValue input output) →ₗ[ℂ]
      (C(ClosedDisk, ComplexEuclidean input) →L[ℂ] C(ClosedDisk, ComplexEuclidean output)) :=
    { toFun := cMapAction
      map_add' := by
        intro first second
        apply ContinuousLinearMap.ext
        intro field
        apply ContinuousMap.ext
        intro point
        rfl
      map_smul' := by
        intro scalar coefficient
        apply ContinuousLinearMap.ext
        intro field
        apply ContinuousMap.ext
        intro point
        rfl }
  exact @LinearMap.mkContinuous ℂ ℂ (C(ClosedDisk, OperatorValue input output))
    (C(ClosedDisk, ComplexEuclidean input) →L[ℂ] C(ClosedDisk, ComplexEuclidean output))
    _ _ _ _ _ _ (RingHom.id ℂ) mapping 1 (fun coefficient => by
      change ‖cMapAction coefficient‖ ≤ 1 * ‖coefficient‖
      rw [one_mul]
      exact cMapAction_norm_le coefficient)

end Grad.GaugeCoefficients.Physical.RadialLedger
