import AKAY21GenuineRadialProjection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000

open Set MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.WeightedJets Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.WeightedJets.SpatialMultiplier

def startupReflectionTest (test : TestFunction openUnitDisk) : TestFunction openUnitDisk where
  toFun := fun point => test.toFun (cartesianReflectionEquiv point)
  smooth := test.smooth.comp cartesianReflectionEquiv.toContinuousLinearEquiv.toContinuousLinearMap.contDiff
  compact := test.compact.comp_homeomorph cartesianReflectionEquiv.toHomeomorph
  supported := by
    intro point member
    have inside := test.supported (tsupport_comp_subset_preimage test.toFun cartesianReflectionEquiv.continuous member)
    change ‖point‖ < 1
    change ‖cartesianReflectionEquiv point‖ < 1 at inside
    simpa only [LinearIsometryEquiv.norm_map] using inside

/-- The literal component of the transpose of covariant rotation averaging. -/
def startupAverageTestComponent (target source : Fin 2) (test : TestFunction openUnitDisk) : TestFunction openUnitDisk :=
  startupAngularCompactTest (fun angle => startupInverseRotationEntry source target (-angle))
    ((startupInverseRotationEntry_smooth source target).comp contDiff_id.neg) test

/-- Qrad transpose on e_source*test, as the nonsingular reflection formula
I-(I+S)A/2. Both source and target refer to Cartesian planar coordinates. -/
def startupQradTestComponent (target source : Fin 2) (test : TestFunction openUnitDisk) : TestFunction openUnitDisk :=
  startupSubTest (multiplyTest (fun _ : Spatial => if target = source then 1 else 0) contDiff_const test)
    (multiplyTest (fun _ : Spatial => (1 / 2 : ℝ)) contDiff_const
      (startupAddTest (startupAverageTestComponent target source test)
        (multiplyTest (fun _ : Spatial => if source = 0 then 1 else -1) contDiff_const
          (startupAverageTestComponent target source (startupReflectionTest test)))))

/-- Radial multiplication commutes with every actual compact angular test. -/
theorem startupAngularCompactTest_radial_product (weight : ℝ → ℝ) (weightSmooth : ContDiff ℝ ∞ weight)
    (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (radial : ∀ angle point, scalar (planeRotationEquiv angle point) = scalar point)
    (test : TestFunction openUnitDisk) :
    startupAngularCompactTest weight weightSmooth (multiplyTest scalar smooth test) =
      multiplyTest scalar smooth (startupAngularCompactTest weight weightSmooth test) := by
  apply startupTest_ext
  intro point
  change startupAngularTest weight (fun source => scalar source * test.toFun source) point =
    scalar point * startupAngularTest weight test.toFun point
  unfold startupAngularTest
  have integrands : (fun angle => weight angle * (scalar (planeRotationEquiv (-angle) point) *
      test.toFun (planeRotationEquiv (-angle) point))) =
      fun angle => scalar point * (weight angle * test.toFun (planeRotationEquiv (-angle) point)) := by
    funext angle
    rw [radial (-angle) point]
    ring
  rw [integrands, integral_const_mul]
  ring

theorem startupReflectionTest_radial_product (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (reflected : ∀ point, scalar (cartesianReflectionEquiv point) = scalar point)
    (test : TestFunction openUnitDisk) :
    startupReflectionTest (multiplyTest scalar smooth test) =
      multiplyTest scalar smooth (startupReflectionTest test) := by
  apply startupTest_ext
  intro point
  change scalar (cartesianReflectionEquiv point) * test.toFun (cartesianReflectionEquiv point) = _
  rw [reflected point]
  rfl

/-- The actual compact Qrad test commutes with every radial axis cutoff. -/
theorem startupQradTestComponent_radial_product (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (radial : ∀ angle point, scalar (planeRotationEquiv angle point) = scalar point)
    (reflected : ∀ point, scalar (cartesianReflectionEquiv point) = scalar point)
    (target source : Fin 2) (test : TestFunction openUnitDisk) :
    startupQradTestComponent target source (multiplyTest scalar smooth test) =
      multiplyTest scalar smooth (startupQradTestComponent target source test) := by
  have first := startupAngularCompactTest_radial_product
    (fun angle => startupInverseRotationEntry source target (-angle))
    ((startupInverseRotationEntry_smooth source target).comp contDiff_id.neg) scalar smooth radial test
  have second := startupAngularCompactTest_radial_product
    (fun angle => startupInverseRotationEntry source target (-angle))
    ((startupInverseRotationEntry_smooth source target).comp contDiff_id.neg) scalar smooth radial (startupReflectionTest test)
  unfold startupQradTestComponent startupAverageTestComponent
  rw [startupReflectionTest_radial_product scalar smooth reflected test, first, second]
  apply startupTest_ext
  intro point
  simp only [startupSubTest, startupAddTest, multiplyTest, Pi.sub_apply, Pi.add_apply]
  ring

/-- Minimal genuine projected physical force equation, before the quotient
and angular inverse are constructed. Xi is the original mean-free scalar.
The correction is literally 2(R F_C,perp)^T U and covariant is F_C^T U. -/
def StartupOriginalProjectedForce (xi : ℤ → Spatial → ℂ)
    (covariant quarterCovariant force correction : Fin 2 → ℤ → Spatial → ℂ) : Prop :=
  ∀ (cell : ℤ) (source : Fin 2) (test : TestFunction openUnitDisk),
    (∑ target : Fin 2, startupRawPairing (force target) cell (startupQradTestComponent target source test)) =
      ∑ target : Fin 2, (
        -startupRawPairing xi cell (startupDerivativeTest target (startupQradTestComponent target source test)) +
        startupRawPairing (covariant target) cell (startupRotationTest (startupQradTestComponent target source test)) -
        startupRawPairing (quarterCovariant target) cell (startupQradTestComponent target source test) +
        startupRawPairing (correction target) cell (startupQradTestComponent target source test))

end Grad.CartesianStartup
