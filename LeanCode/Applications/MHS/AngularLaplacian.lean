import AngularProjectionL2

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace Grad.Constraints

open Grad.ClosedJets Grad.GaugeCoefficients.Radial Grad.RepresentedKernel.SpatialProduct

def closedLaplacianValue {dimension : ℕ} (field : ClosedJet dimension) (point : ClosedDisk) :
    ComplexEuclidean dimension :=
  closedDerivative field 2 (fun _ => 0) point + closedDerivative field 2 (fun _ => 1) point

theorem rotation_two_chain_trace (angle : ℝ) (word : CartesianWord 2) :
    chainFactor 2 (planeRotationEquiv angle) (fun _ => 0) word +
      chainFactor 2 (planeRotationEquiv angle) (fun _ => 1) word =
        if word 0 = word 1 then 1 else 0 := by
  simp only [chainFactor_eq, Fin.prod_univ_two]
  generalize word 0 = firstIndex
  generalize word 1 = secondIndex
  fin_cases firstIndex <;> fin_cases secondIndex
  all_goals simp [planeRotationEquiv_apply, planeRotation,
    Grad.PDEBootstrap.spatialDirection]
  all_goals nlinarith [Real.sin_sq_add_cos_sq angle]

theorem orthogonalDerivative_rotation_laplacian {dimension : ℕ} (angle : ℝ)
    (field : ClosedJet dimension) (point : ClosedDisk) :
    orthogonalDerivative (planeRotationEquiv angle) field 2 (fun _ => 0) point +
      orthogonalDerivative (planeRotationEquiv angle) field 2 (fun _ => 1) point =
        closedLaplacianValue field (rotatedPoint angle point) := by
  change (∑ target : CartesianWord 2, chainFactor 2 (planeRotationEquiv angle) (fun _ => 0) target •
    closedDerivative field 2 target (orthogonalClosedPoint (planeRotationEquiv angle) point)) +
    (∑ target : CartesianWord 2, chainFactor 2 (planeRotationEquiv angle) (fun _ => 1) target •
    closedDerivative field 2 target (orthogonalClosedPoint (planeRotationEquiv angle) point)) = _
  rw [← Finset.sum_add_distrib]
  simp_rw [← add_smul, rotation_two_chain_trace]
  have words : (Finset.univ : Finset (CartesianWord 2)) =
      {![0, 0], ![0, 1], ![1, 0], ![1, 1]} := by decide
  rw [words]
  simp [closedLaplacianValue]
  have firstWord : (![0, 0] : CartesianWord 2) = (fun _ => 0) := by
    funext position
    fin_cases position <;> rfl
  have secondWord : (![1, 1] : CartesianWord 2) = (fun _ => 1) := by
    funext position
    fin_cases position <;> rfl
  rw [firstWord, secondWord]
  rfl

theorem angularClosedJet_laplacian_origin {dimension : ℕ} (field : ClosedJet dimension) :
    closedLaplacianValue (angularClosedJet 0 field) ⟨0, by simp [closedUnitDisk]⟩ =
      closedLaplacianValue field ⟨0, by simp [closedUnitDisk]⟩ := by
  let origin : ClosedDisk := ⟨0, by simp [closedUnitDisk]⟩
  have firstContinuous := (ContinuousMap.evalCLM ℝ origin).continuous.comp
    (angularDerivativeFamily_continuous 0 field (fun _ : Fin 2 => 0))
  have secondContinuous := (ContinuousMap.evalCLM ℝ origin).continuous.comp
    (angularDerivativeFamily_continuous 0 field (fun _ : Fin 2 => 1))
  have firstIntegrable : IntegrableOn
      (fun angle => angularCharacter 0 angle •
        orthogonalDerivative (planeRotationEquiv angle) field 2 (fun _ => 0) origin)
      (Icc (0 : ℝ) (2 * Real.pi)) := firstContinuous.continuousOn.integrableOn_Icc
  have secondIntegrable : IntegrableOn
      (fun angle => angularCharacter 0 angle •
        orthogonalDerivative (planeRotationEquiv angle) field 2 (fun _ => 1) origin)
      (Icc (0 : ℝ) (2 * Real.pi)) := secondContinuous.continuousOn.integrableOn_Icc
  unfold closedLaplacianValue
  rw [angularClosedJet_derivative, angularClosedJet_derivative, ← smul_add,
    ← integral_add firstIntegrable secondIntegrable]
  have identity (angle : ℝ) :
      angularCharacter 0 angle • orthogonalDerivative (planeRotationEquiv angle) field 2 (fun _ => 0) origin +
        angularCharacter 0 angle • orthogonalDerivative (planeRotationEquiv angle) field 2 (fun _ => 1) origin =
          closedLaplacianValue field origin := by
    rw [angularCharacter_zero_mode, one_smul, one_smul, orthogonalDerivative_rotation_laplacian]
    congr 1
    apply Subtype.ext
    change planeRotation angle 0 = 0
    exact (planeRotationEquiv angle).map_zero
  change (2 * Real.pi)⁻¹ • (∫ angle in Icc (0 : ℝ) (2 * Real.pi), _) = closedLaplacianValue field origin
  simp_rw [identity]
  rw [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
    sub_zero, ENNReal.toReal_ofReal (by positivity)]
  rw [smul_smul, inv_mul_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), one_smul]

end Grad.Constraints
