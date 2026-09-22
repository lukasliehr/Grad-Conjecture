import ANR1Distribution
import AngularLaplacian

noncomputable section
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ContDiff BigOperators

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.NonlinearDivision (laplacianJet laplacianJet_value)
open Grad.GaugeCoefficients.Physical.Compensated (partialJetLinear)

/-- Rotational invariance of the Cartesian Laplacian is valid at every
closed-disk point and every angular mode, including the axis. -/
theorem angularClosedJet_laplacian (mode : ℤ) (field : ClosedJet 1) (point : ClosedDisk) :
    closedLaplacianValue (angularClosedJet mode field) point =
      (2 * Real.pi)⁻¹ • ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
        angularCharacter mode angle • closedLaplacianValue field (rotatedPoint angle point) := by
  have firstIntegrable : IntegrableOn
      (fun angle => angularCharacter mode angle • orthogonalDerivative
        (planeRotationEquiv angle) field 2 (fun _ => 0) point)
      (Icc (0 : ℝ) (2 * Real.pi)) :=  ((ContinuousMap.evalCLM ℝ point).continuous.comp
    (angularDerivativeFamily_continuous mode field (fun _ : Fin 2 => 0))).continuousOn.integrableOn_Icc
      (a := (0 : ℝ)) (b := 2 * Real.pi)
  have secondIntegrable : IntegrableOn
      (fun angle => angularCharacter mode angle • orthogonalDerivative
        (planeRotationEquiv angle) field 2 (fun _ => 1) point)
      (Icc (0 : ℝ) (2 * Real.pi)) :=  ((ContinuousMap.evalCLM ℝ point).continuous.comp
    (angularDerivativeFamily_continuous mode field (fun _ : Fin 2 => 1))).continuousOn.integrableOn_Icc
      (a := (0 : ℝ)) (b := 2 * Real.pi)
  unfold closedLaplacianValue
  rw [angularClosedJet_derivative, angularClosedJet_derivative, ← smul_add,
    ← integral_add firstIntegrable secondIntegrable]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro angle _
  dsimp only
  rw [← smul_add, orthogonalDerivative_rotation_laplacian]
  rfl

theorem laplacianJet_angular (mode : ℤ) (field : ClosedJet 1) :
    laplacianJet (angularClosedJet mode field) = angularClosedJet mode (laplacianJet field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [laplacianJet_value, angularClosedJet_value]
  change closedLaplacianValue (angularClosedJet mode field) point = _
  rw [angularClosedJet_laplacian, intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi), ← integral_Icc_eq_integral_Ioc]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro angle _
  rw [laplacianJet_value]
  rfl

def laplacianJetLinear : ClosedJet 1 →ₗ[ℂ] ClosedJet 1 :=
  (partialJetLinear 1 0).comp (partialJetLinear 1 0) +
    (partialJetLinear 1 1).comp (partialJetLinear 1 1)

theorem laplacianJetLinear_apply (field : ClosedJet 1) :
    laplacianJetLinear field = laplacianJet field := rfl

theorem laplacianJet_excluded (modes : Finset ℤ) (field : ClosedJet 1) :
    laplacianJet (excludedAngularJet modes field) = excludedAngularJet modes (laplacianJet field) := by
  change laplacianJetLinear (field - selectedAngularJet modes field) =
    laplacianJet field - selectedAngularJet modes (laplacianJet field)
  rw [map_sub, selectedAngularJet_eq, map_sum, selectedAngularJet_eq]
  simp only [laplacianJetLinear_apply, laplacianJet_angular]

end Grad.CircularHighRegularity
