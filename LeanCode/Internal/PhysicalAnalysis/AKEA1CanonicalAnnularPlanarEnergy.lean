import AKDX13ActualAnnularPlanarNorm
import AKDZ5CanonicalFiniteCellDensity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology ENNReal
namespace Grad.OriginalCollarNorm
open Grad.Constraints Grad.ClosedJets Grad.CartesianState Grad.CartesianStartup
open Grad.OriginalCoreRealization Grad.ActualOriginalSourceMoments Grad.OriginalCartesianTameEstimate
open Grad.BoundaryTrace Grad.BoundaryLift Grad.AnnularGeneralSourceRegularity

theorem actualNativeAnnularCutoff_zero_on_smaller (lower : ℝ) (small : lower≤(1/8:ℝ))
    (point : SpatialPlane) (inside : ‖point‖<2*lower) : actualNativeAnnularCutoff point=0 :=
  actualNativeAnnularCutoff_zero_inner point (by linarith)

/-- Actual canonical Euler energies control the original planar norm of
the SAME existing annular cutoff on any fixed collar inside radius one eighth. -/
theorem canonicalAnnular_planarEnergy (lower : ℝ) (positive : 0<lower)
    (bounded : lower<1) (small : lower≤(1/8:ℝ)) (grade : ℕ) :
    ∃ constant : ℝ,0≤constant ∧ ∀ (parameters : PhaseParameters) (core image : ACore parameters 3),
      (originalSourceMoments parameters image).field=
        startupCutoffL2 actualNativeAnnularCutoff actualNativeAnnularCutoff_smooth
          actualNativeAnnularCutoff_compact (originalSourceMoments parameters core).field →
      ∀ payment : ℝ,0≤payment →
      (∀ power rank,power+rank≤grade →
        (∫⁻ radius in Icc lower 1,ENNReal.ofReal
          (‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank
            (cartesianWeightedRadialCurve parameters lower positive bounded core power 0) radius‖^2))≤
          ENNReal.ofReal (payment^2)) →
      originalPlanarNorm parameters grade image≤constant*payment := by
  let rows := sameOriginalCutoff_planarNorm lower positive bounded
    actualNativeAnnularCutoff actualNativeAnnularCutoff_smooth actualNativeAnnularCutoff_compact
    (actualNativeAnnularCutoff_zero_on_smaller lower small) grade
  let density := canonicalPolarDensityConstant lower grade
  have density0 : 0≤density := canonicalPolarDensityConstant_nonnegative lower grade
  refine ⟨rows.choose*Real.sqrt density,mul_nonneg rows.choose_spec.1 (Real.sqrt_nonneg _),?_⟩
  intro parameters core image same payment payment0 energy
  have normBound := rows.choose_spec.2 parameters core image same
    (Real.sqrt density*payment) (mul_nonneg (Real.sqrt_nonneg _) payment0) (fun cells => ?_)
  · exact normBound.trans_eq (mul_assoc _ _ _).symm
  · rw [mul_pow,Real.sq_sqrt density0]
    exact canonicalFiniteCell_polarDensity parameters lower positive bounded grade core payment payment0 energy cells

end Grad.OriginalCollarNorm
