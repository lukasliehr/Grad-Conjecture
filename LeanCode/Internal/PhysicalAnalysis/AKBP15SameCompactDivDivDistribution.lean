import AKBP14WholePlaneDistributionPairings

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set MeasureTheory LineDeriv
open scoped ContDiff SchwartzMap
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets Grad.WeightedJets.ZeroExtension
open Grad.RepresentedKernel.SpatialProduct

theorem startupLaplacian_distribution_sum (distribution : FieldDistribution) :
    Laplacian.laplacian distribution =
      ∑ direction : Fin 2, distributionDerivative direction (distributionDerivative direction distribution) := by
  have basis (direction : Fin 2) : (EuclideanSpace.basisFun (Fin 2) ℝ) direction = spatialDirection direction := by
    apply PiLp.ext
    intro coordinate
    simp [EuclideanSpace.basisFun_apply,spatialDirection]
  have formula := TemperedDistribution.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 2) ℝ) distribution
  simp_rw [basis] at formula
  exact formula

/-- The SAME compactly supported rough equation becomes a genuine whole-plane
tempered identity. The flux sign comes from distributional integration by
parts, with all cells, two spatial derivatives and complex tests retained. -/
theorem startupCompact_divDiv_distribution {support : Set Spatial}
    (localizer : TestLocalizer openUnitDisk support) (field zeroth : StartupL2 3)
    (tensor : Fin 2 → Fin 2 → StartupL2 3) (flux : Fin 2 → StartupL2 3)
    (fieldSupported : SupportedField (CellValues 3) openUnitDisk support field)
    (zeroSupported : SupportedField (CellValues 3) openUnitDisk support zeroth)
    (tensorSupported : ∀ outer inner, SupportedField (CellValues 3) openUnitDisk support (tensor outer inner))
    (fluxSupported : ∀ direction, SupportedField (CellValues 3) openUnitDisk support (flux direction))
    (equation : StartupWeakDivDivEquation field zeroth tensor flux) :
    Laplacian.laplacian (distributionEmbedding (startupPlaneExtension field)) =
      (∑ outer : Fin 2, ∑ inside : Fin 2, distributionDerivative outer
        (distributionDerivative inside (distributionEmbedding (startupPlaneExtension (tensor outer inside))))) +
      distributionEmbedding (startupPlaneExtension zeroth) -
      ∑ direction : Fin 2, distributionDerivative direction (distributionEmbedding (startupPlaneExtension (flux direction))) := by
  rw [startupLaplacian_distribution_sum]
  apply startupTempered_eq_of_real
  intro test
  apply lp.ext
  funext cell
  apply ext_inner_left ℂ
  intro vector
  simp only [Fin.sum_univ_two,add_apply,sub_apply,lp.coeFn_add,lp.coeFn_sub,Pi.add_apply,Pi.sub_apply,
    inner_add_right,inner_sub_right,startupPlaneExtension_second_realSchwartz,startupPlaneExtension_realSchwartz,
    startupPlaneExtension_first_realSchwartz]
  have identity := startupCompactEquation_smoothTests localizer field zeroth tensor flux
    fieldSupported zeroSupported tensorSupported fluxSupported equation cell vector test test.smooth'
  simp only [Fin.sum_univ_two] at identity
  linear_combination identity

end Grad.CartesianStartup
