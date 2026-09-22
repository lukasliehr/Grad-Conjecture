import AKBP13CompactEquationSmoothTests

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory LineDeriv
open scoped ContDiff SchwartzMap
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets Grad.WeightedJets.ZeroExtension
open Grad.RepresentedKernel.SpatialProduct Grad.NonlinearQuotient

theorem startupPlaneExtension_realSchwartz (field : StartupL2 3) (test : 𝓢(Spatial, ℝ))
    (cell : ℤ) (vector : PhysicalValue 3) :
    inner ℂ vector ((distributionEmbedding (startupPlaneExtension field) (startupRealSchwartz test)) cell) =
      startupSmoothPairing field cell vector test := by
  change inner ℂ vector ((distributionEmbedding (startupWholePlaneField
    (fieldExtension (CellValues 3) openUnitDisk openUnitDisk_isOpen.measurableSet field)) (startupRealSchwartz test)) cell) = _
  rw [startupRealSchwartz_pairing,integral_extension]
  rfl

theorem startupRealSchwartz_derivative_distribution (distribution : FieldDistribution)
    (test : 𝓢(Spatial, ℝ)) (direction : Fin 2) :
    distributionDerivative direction distribution (startupRealSchwartz test) =
      -distribution (startupRealSchwartz (lineDerivOp (spatialDirection direction) test)) := by
  change (lineDerivOp (spatialDirection direction) distribution) (startupRealSchwartz test) = _
  rw [TemperedDistribution.lineDerivOp_apply_apply,map_neg,startupRealSchwartz_derivative]

theorem startupSchwartz_direction (test : 𝓢(Spatial, ℝ)) (direction : Fin 2) :
    (lineDerivOp (spatialDirection direction) test : Spatial → ℝ) = directionDerivative direction test := by
  funext point
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rfl

theorem startupPlaneExtension_first_realSchwartz (field : StartupL2 3) (test : 𝓢(Spatial, ℝ))
    (cell : ℤ) (vector : PhysicalValue 3) (direction : Fin 2) :
    inner ℂ vector ((distributionDerivative direction (distributionEmbedding (startupPlaneExtension field))
      (startupRealSchwartz test)) cell) =
      -startupSmoothPairing field cell vector (directionDerivative direction test) := by
  rw [startupRealSchwartz_derivative_distribution]
  simp only [lp.coeFn_neg,Pi.neg_apply,inner_neg_right]
  rw [startupPlaneExtension_realSchwartz]
  exact congrArg (fun function : Spatial → ℝ => -startupSmoothPairing field cell vector function)
    (startupSchwartz_direction test direction)

theorem startupPlaneExtension_second_realSchwartz (field : StartupL2 3) (test : 𝓢(Spatial, ℝ))
    (cell : ℤ) (vector : PhysicalValue 3) (outer inside : Fin 2) :
    inner ℂ vector ((distributionDerivative outer (distributionDerivative inside (distributionEmbedding (startupPlaneExtension field)))
      (startupRealSchwartz test)) cell) =
      startupSmoothPairing field cell vector (directionDerivative outer (directionDerivative inside test)) := by
  rw [startupRealSchwartz_derivative_distribution,startupRealSchwartz_derivative_distribution,neg_neg,
    startupPlaneExtension_realSchwartz]
  rw [startupSchwartz_direction,startupSchwartz_direction]
  apply congrArg (startupSmoothPairing field cell vector)
  funext point
  exact directionDerivative_commute isOpen_univ inside outer test.smooth'.contDiffOn (mem_univ point)

end Grad.CartesianStartup
