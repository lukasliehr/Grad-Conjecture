import AIM1OrdinaryCoreExtension

noncomputable section
open scoped ContDiff
namespace Grad.OrdinaryDiskCalculus
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.InteriorLocalization Grad.PDEBootstrap
attribute [local instance] unitNormedSpace

def productJetLinear (coefficient : SmoothOperatorJet 1 1) : ClosedJet 1 →ₗ[ℂ] ClosedJet 1 where
  toFun := apProductJet coefficient
  map_add' first second := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    simp only [apProductJet_value, closedJet_value_add, ContinuousMap.add_apply, map_add]
  map_smul' scalar field := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    simp only [apProductJet_value, closedJet_value_smul, ContinuousMap.smul_apply, map_smul, RingHom.id_apply]

theorem unitProduct_exists (grade : ℕ) (coefficient : SmoothOperatorJet 1 1) :
    ∃ completed : unitDiskSobolev grade →L[ℂ] unitDiskSobolev grade,
      (∀ core, completed (unitDiskCoreInto grade core) = unitDiskCoreInto grade (apProductJet coefficient core)) ∧
      (∀ field, ‖completed field‖ ≤ unitProductConstant grade coefficient * ‖field‖) :=
  unitCore_extension grade grade (productJetLinear coefficient) _
    (unitProductConstant_nonnegative grade coefficient) (unitProduct_bound grade coefficient)

def unitProduct (grade : ℕ) (coefficient : SmoothOperatorJet 1 1) :
    unitDiskSobolev grade →L[ℂ] unitDiskSobolev grade :=
  (unitProduct_exists grade coefficient).choose

theorem unitProduct_core (grade : ℕ) (coefficient : SmoothOperatorJet 1 1) (core : ClosedJet 1) :
    unitProduct grade coefficient (unitDiskCoreInto grade core) = unitDiskCoreInto grade (apProductJet coefficient core) :=
  (unitProduct_exists grade coefficient).choose_spec.1 core

theorem unitProduct_bound (grade : ℕ) (coefficient : SmoothOperatorJet 1 1) (field : unitDiskSobolev grade) :
    ‖unitProduct grade coefficient field‖ ≤ unitProductConstant grade coefficient * ‖field‖ :=
  (unitProduct_exists grade coefficient).choose_spec.2 field

def unitScalar (grade : ℕ) (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar) :
    unitDiskSobolev grade →L[ℂ] unitDiskSobolev grade :=
  unitProduct grade (apScalarOperatorJet 1 scalar smooth)

theorem productCore_L2 (coefficient : SmoothOperatorJet 1 1) (core : ClosedJet 1) :
    closedL2Core (apProductJet coefficient core) = closedOperatorL2 coefficient.value (closedL2Core core) := by
  change closedContinuousToDiskL2 (apProductJet coefficient core).value =
    closedOperatorL2 coefficient.value (closedContinuousToDiskL2 core.value)
  rw [closedOperatorL2_closed]
  apply congrArg closedContinuousToDiskL2
  apply ContinuousMap.ext
  intro point
  exact apProductJet_value coefficient core point

theorem unitProduct_bulk (grade : ℕ) (coefficient : SmoothOperatorJet 1 1) (field : unitDiskSobolev grade) :
    unitDiskBulk grade (unitProduct grade coefficient field) =
      closedOperatorL2 coefficient.value (unitDiskBulk grade field) := by
  apply isClosed_property (unitDiskCoreInto_denseRange grade)
    (isClosed_eq ((unitDiskBulk grade).continuous.comp (unitProduct grade coefficient).continuous)
      ((closedOperatorL2 coefficient.value).continuous.comp (unitDiskBulk grade).continuous)) _ field
  intro core
  exact (congrArg (unitDiskBulk grade) (unitProduct_core grade coefficient core)).trans
    ((unitDiskBulk_core grade (apProductJet coefficient core)).trans
      ((productCore_L2 coefficient core).trans
        (congrArg (closedOperatorL2 coefficient.value) (unitDiskBulk_core grade core).symm)))

theorem unitScalar_bulk (grade : ℕ) (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (field : unitDiskSobolev grade) :
    unitDiskBulk grade (unitScalar grade scalar smooth field) = diskScalar scalar smooth (unitDiskBulk grade field) :=
  unitProduct_bulk grade (apScalarOperatorJet 1 scalar smooth) field

theorem unitScalar_bound (grade : ℕ) (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (field : unitDiskSobolev grade) :
    ‖unitScalar grade scalar smooth field‖ ≤ unitProductConstant grade (apScalarOperatorJet 1 scalar smooth) * ‖field‖ :=
  unitProduct_bound grade _ field

end Grad.OrdinaryDiskCalculus
