import AKDB1GenuineScalarRotationRecovery

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.WeightedJets.SpatialMultiplier

private theorem smoothDiskDerivative_bound (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (index : ℕ×ℕ) : ∃ bound : NNReal, ∀ point ∈ openUnitDisk,
      |scalarDerivative index scalar point| ≤ bound := by
  obtain ⟨bound,bounded⟩ := (isCompact_closedBall (0 : Spatial) 1).exists_bound_of_continuousOn
    (scalarDerivative_smooth index scalar smooth).continuous.continuousOn
  refine ⟨⟨max 0 bound,le_max_left _ _⟩,fun point member => ?_⟩
  have inside : point ∈ Metric.closedBall (0 : Spatial) 1 := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using member.le
  have actual : |scalarDerivative index scalar point| ≤ bound := by
    simpa only [Real.norm_eq_abs] using bounded point inside
  exact actual.trans (le_max_right _ _)

/-- A polynomial coordinate needs no new cutoff: every derivative is bounded
on the original closed unit disk. The existing graph multiplier is reused. -/
def startupSmoothDiskSymbol (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (order : ℕ) : Symbol order openUnitDisk where
  toFun := scalar
  smooth := smooth
  bound index := (smoothDiskDerivative_bound scalar smooth index.val).choose
  derivative_bound index := (smoothDiskDerivative_bound scalar smooth index.val).choose_spec

def startupSmoothDiskMultiplier (dimension : ℕ) (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar) :
    StartupL2 dimension →L[ℂ] StartupL2 dimension :=
  fieldMultiplier dimension openUnitDisk openUnitDisk_isOpen
    (derivativeScalar (startupSmoothDiskSymbol scalar smooth 0) (zeroIndex 0))

theorem startupSmoothDiskMultiplier_same (dimension : ℕ) (scalar : Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ scalar) (field : StartupL2 dimension) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell,
      startupSmoothDiskMultiplier dimension scalar smooth field point cell = (scalar point : ℂ) • field point cell :=
  fieldMultiplier_ae dimension openUnitDisk openUnitDisk_isOpen _ field

theorem startupSmoothDiskMultiplier_pairing (dimension : ℕ) (scalar : Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ scalar) (field : StartupL2 dimension)
    (cell : ℤ) (coordinate : Fin dimension) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell coordinate test (startupSmoothDiskMultiplier dimension scalar smooth field) =
      startupCoordinateTestPairing cell coordinate (multiplyTest scalar smooth test) field :=
  fieldMultiplier_pairing dimension openUnitDisk openUnitDisk_isOpen _ field cell (EuclideanSpace.single coordinate 1) test

theorem startupSmoothDiskMultiplier_preservesGraph (dimension : ℕ) (scalar : Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ scalar) : StartupPreservesGraph (startupSmoothDiskMultiplier dimension scalar smooth) := by
  intro order weight field
  refine ⟨graphMultiplier dimension order weight openUnitDisk openUnitDisk_isOpen
    (startupSmoothDiskSymbol scalar smooth order) field,?_⟩
  rw [show graphMultiplier dimension order weight openUnitDisk openUnitDisk_isOpen
      (startupSmoothDiskSymbol scalar smooth order) =
    jetMultiplier dimension order openUnitDisk openUnitDisk_isOpen (startupSmoothDiskSymbol scalar smooth order)
      (fun _ => weight) (constantExponent_antitone order weight) from rfl,jetMultiplier_base_apply]
  rw [fieldMultiplier_congr dimension openUnitDisk openUnitDisk_isOpen
    (derivativeScalar (startupSmoothDiskSymbol scalar smooth order) (zeroIndex order))
    (derivativeScalar (startupSmoothDiskSymbol scalar smooth 0) (zeroIndex 0)) rfl]
  rfl

end Grad.CartesianStartup
