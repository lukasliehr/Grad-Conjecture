import AKAA31OriginalB10KernelConsumer
import ZE1Compact

noncomputable section

set_option maxHeartbeats 1500000

open MeasureTheory
open scoped ContDiff Topology

namespace Grad.CartesianStartup

open Grad.GenericCarriers Grad.WeightedJets Grad.WeightedJets.ZeroExtension
open Grad.WeakTesting Grad.WeakTesting.Commutation

/-- A compact localizer permits every smooth real test when both members
 of a genuine weak derivative pair have the same compact support. -/
def startupLocalizeSmoothTest {domain support : Set Grad.PDEBootstrap.Spatial}
    (localizer : TestLocalizer domain support) (test : Grad.PDEBootstrap.Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) : TestFunction domain where
  toFun := fun point => localizer.cutoff.toFun point * test point
  smooth := localizer.cutoff.smooth.mul smooth
  compact := localizer.cutoff.compact.mul_right
  supported := tsupport_mul_subset_left.trans localizer.cutoff.supported

theorem startupLocalizeSmoothTest_germ {domain support : Set Grad.PDEBootstrap.Spatial}
    (localizer : TestLocalizer domain support) (test : Grad.PDEBootstrap.Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) (point : Grad.PDEBootstrap.Spatial) (inside : point ∈ support) :
    (startupLocalizeSmoothTest localizer test smooth).toFun =ᶠ[𝓝 point] test := by
  filter_upwards [localizer.one_near point inside] with source oneAt
  change localizer.cutoff.toFun source * test source = test source
  rw [oneAt, one_mul]

theorem startupLocalizeSmoothTest_ordered {domain support : Set Grad.PDEBootstrap.Spatial}
    (localizer : TestLocalizer domain support) (test : Grad.PDEBootstrap.Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) (rank : ℕ) (word : Fin rank → Fin 2)
    (point : Grad.PDEBootstrap.Spatial) (inside : point ∈ support) :
    orderedTestDerivative rank word (startupLocalizeSmoothTest localizer test smooth).toFun point =
      orderedTestDerivative rank word test point :=
  congrArg (fun multilinear => multilinear (fun position => Grad.PDEBootstrap.spatialDirection (word position)))
    ((startupLocalizeSmoothTest_germ localizer test smooth point inside).iteratedFDeriv ℝ rank).eq_of_nhds

theorem startupCompactWeak_smoothTest {dimension rank : ℕ}
    {domain support : Set Grad.PDEBootstrap.Spatial} (localizer : TestLocalizer domain support)
    (word : Fin rank → Fin 2) (field derivative : FieldL2 dimension domain)
    (fieldSupported : SupportedField (CellValues dimension) domain support field)
    (derivativeSupported : SupportedField (CellValues dimension) domain support derivative)
    (weak : HasWeakOrderedDerivative dimension domain rank word field derivative)
    (cell : ℤ) (vector : PhysicalValue dimension) (test : Grad.PDEBootstrap.Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) :
    (∫ point in domain, test point • inner ℂ vector (derivative point cell)) =
      ((-1 : ℂ) ^ rank) * ∫ point in domain,
        orderedTestDerivative rank word test point • inner ℂ vector (field point cell) := by
  let localized := startupLocalizeSmoothTest localizer test smooth
  have identity := (hasWeakOrderedDerivative_iff_integral dimension domain rank word field derivative).mp weak
    cell vector localized.toFun localized.smooth localized.compact localized.supported
  have same : Set.EqOn localized.toFun test support :=
    fun point inside => (startupLocalizeSmoothTest_germ localizer test smooth point inside).eq_of_nhds
  have sameDerivative : Set.EqOn (orderedTestDerivative rank word localized.toFun)
      (orderedTestDerivative rank word test) support :=
    fun point inside => startupLocalizeSmoothTest_ordered localizer test smooth rank word point inside
  rw [integral_supported_congr dimension domain support derivative derivativeSupported cell vector _ _ same,
    integral_supported_congr dimension domain support field fieldSupported cell vector _ _ sameDerivative] at identity
  exact identity

end Grad.CartesianStartup
