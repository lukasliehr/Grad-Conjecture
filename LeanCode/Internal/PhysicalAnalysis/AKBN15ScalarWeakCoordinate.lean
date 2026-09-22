import AKBN14ActualProjectedThirdMoments

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.RepresentedKernel.SpatialProduct Grad.ActualSmoothPhysicalField
open Grad.ActualCartesianWeakEquations Grad.WeightedAxisRemoval

theorem startupScalar_integral_coordinate (field : Spatial → ComplexEuclidean 1)
    (integrable : IntegrableOn field openUnitDisk) :
    (∫ point in openUnitDisk, field point) 0 = ∫ point in openUnitDisk, field point 0 :=
  ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).integral_comp_comm integrable).symm

/-- Extract the actual scalar coordinate after vector-valued compact
integration; all interchanges use the original flux integrability. -/
theorem startupAngularWeak_coordinate (field source : Spatial → ComplexEuclidean 1)
    (fieldIntegrable : IntegrableOn field openUnitDisk)
    (weightedIntegrable : IntegrableOn (fun point => ‖point‖⁻¹ * ‖field point‖) openUnitDisk)
    (sourceIntegrable : IntegrableOn source openUnitDisk)
    (test : TestFunction openUnitDisk)
    (weak : (∫ point in openUnitDisk, test.toFun point • source point) =
      -(∑ direction : Fin 2, ∫ point in openUnitDisk,
        directionDerivative direction test.toFun point • angularTransportFlux field direction point)) :
    (∫ point in openUnitDisk, test.toFun point • source point 0) =
      -(∑ direction : Fin 2, ∫ point in openUnitDisk,
        (directionDerivative direction test.toFun point * angularRotationCoordinate direction point) • field point 0) := by
  have sourceTest := compactTest_smul_integrable (volume.restrict openUnitDisk)
    test.toFun test.smooth test.compact source sourceIntegrable
  have flux := angularTransportFlux_integrable_pair field fieldIntegrable weightedIntegrable
  have fluxTest (direction : Fin 2) := compactTest_smul_integrable (volume.restrict openUnitDisk)
    (startupDerivativeTest direction test).toFun (startupDerivativeTest direction test).smooth
    (startupDerivativeTest direction test).compact (angularTransportFlux field direction) (flux direction).1
  have coordinate := congrArg (fun value : ComplexEuclidean 1 => value 0) weak
  rw [startupScalar_integral_coordinate _ sourceTest] at coordinate
  simp only [Fin.sum_univ_two, PiLp.neg_apply, PiLp.add_apply] at coordinate
  have fluxCoordinate (direction : Fin 2) := startupScalar_integral_coordinate _ (fluxTest direction)
  change ∀ direction : Fin 2, (∫ point in openUnitDisk, directionDerivative direction test.toFun point • angularTransportFlux field direction point).ofLp 0 = _ at fluxCoordinate
  rw [fluxCoordinate 0, fluxCoordinate 1] at coordinate
  simpa only [Fin.sum_univ_two,PiLp.smul_apply,angularTransportFlux,smul_smul,startupDerivativeTest] using coordinate

end Grad.CartesianStartup
