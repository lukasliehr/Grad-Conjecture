import ACE18ActualVolterraPoisson

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterVolterra
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearRadial Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.NonlinearDivision (IsRotationInvariant laplacianJet laplacianJet_value)

theorem centerSigned_smul {dimension : ℕ} (sign : ℝ) (scalar : ℂ) (field : ClosedJet dimension) :
    coordinateMultiplyJet sign (scalar • field) = scalar • coordinateMultiplyJet sign field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [coordinateMultiplyJet_value, closedJet_value_smul, ContinuousMap.smul_apply,
    closedJet_value_smul, ContinuousMap.smul_apply, coordinateMultiplyJet_value]
  exact smul_comm _ _ _

theorem centerLaplacian_smul {dimension : ℕ} (scalar : ℂ) (field : ClosedJet dimension) :
    laplacianJet (scalar • field) = scalar • laplacianJet field := by
  simp only [laplacianJet, centerPartial_smul, smul_add]

theorem centerLaplacian_coordinate_value {dimension : ℕ} (sign : ℝ) (field : ClosedJet dimension)
    (point : ClosedDisk) :
    (laplacianJet (coordinateMultiplyJet sign field)).value point =
      signedComplexCoordinate sign point.val • (laplacianJet field).value point +
        (2 : ℂ) • (partialJet 0 field).value point +
          (2 * Complex.I * (sign : ℂ)) • (partialJet 1 field).value point := by
  simp only [laplacianJet, centerCoordinate_decomposition, centerPartial_add, centerPartial_smul,
    centerPartial_coordinate]
  apply PiLp.ext
  intro coordinate
  simp [closedJet_value_add, closedJet_value_smul, coordinateJet_value,
    PiLp.add_apply, PiLp.smul_apply, Complex.real_smul, spatialBasis, signedComplexCoordinate]
  ring

/-- The second-order equation passes through convergence of the actual
Cartesian closed derivatives. No distributional or extension hypothesis is substituted. -/
theorem centerLaplacian_hasSum {dimension : ℕ} (sign : ℝ) (terms : ℕ → ClosedJet dimension)
    (limit : ClosedJet dimension)
    (converges : ∀ order (word : CartesianWord order),
      HasSum (fun count => closedDerivative (terms count) order word) (closedDerivative limit order word))
    (point : ClosedDisk) :
    HasSum (fun count => (laplacianJet (coordinateMultiplyJet sign (terms count))).value point)
      ((laplacianJet (coordinateMultiplyJet sign limit)).value point) := by
  have partialSeries (direction : Fin 2) :
      HasSum (fun count => (partialJet direction (terms count)).value point) ((partialJet direction limit).value point) :=
    (ContinuousMap.evalCLM ℝ point).hasSum (converges 1 (fun _ => direction))
  have laplacianSeries : HasSum (fun count => (laplacianJet (terms count)).value point) ((laplacianJet limit).value point) := by
    have sum := ((ContinuousMap.evalCLM ℝ point).hasSum (converges 2 (fun _ => 0))).add
      ((ContinuousMap.evalCLM ℝ point).hasSum (converges 2 (fun _ => 1)))
    simpa only [laplacianJet_value, laplacianCoefficient, ContinuousMap.add_apply, ContinuousMap.evalCLM_apply] using sum
  have sum := ((laplacianSeries.const_smul (signedComplexCoordinate sign point.val)).add
    ((partialSeries 0).const_smul (2 : ℂ))).add
    ((partialSeries 1).const_smul (2 * Complex.I * (sign : ℂ)))
  simpa only [centerLaplacian_coordinate_value] using sum

theorem volterraResolvent_laplacian_hasSum {dimension : ℕ} (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (parameter : ℝ) (field : ClosedJet dimension) (radial : IsRotationInvariant field) (point : ClosedDisk) :
    HasSum (fun count : ℕ => ((parameter ^ count : ℝ) : ℂ) •
      (coordinateMultiplyJet (mode : ℝ) (volterraPower count field)).value point)
      ((laplacianJet (coordinateMultiplyJet (mode : ℝ) (volterraResolventJet parameter field))).value point) := by
  have sum := centerLaplacian_hasSum (mode : ℝ)
    (fun count => ((parameter ^ count : ℝ) : ℂ) • volterraPower (count + 1) field)
    (volterraResolventJet parameter field) (fun _ word => volterraResolventJet_derivative_hasSum parameter field word) point
  simpa only [centerSigned_smul, centerLaplacian_smul, volterraPower_poisson mode center _ field radial,
    closedJet_value_smul, ContinuousMap.smul_apply] using sum

end Grad.ActualCenterVolterra
