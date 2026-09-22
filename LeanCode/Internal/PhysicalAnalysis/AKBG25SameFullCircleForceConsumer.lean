import AKBG24RawOrbitScalarMean

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.Constraints.Gauges
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets Grad.GaugeCoefficients.Algebra

theorem originalValueKernel_zero (input output : ℕ) :
    originalValueKernel (0 : OperatorValue input output) = 0 := by
  apply norm_le_zero_iff.mp
  change ‖startupPointKernel (0 : OperatorValue input output) (LinearIsometryEquiv.refl ℝ _)‖ ≤ 0
  simpa only [norm_zero] using startupPointKernel_norm (0 : OperatorValue input output) (LinearIsometryEquiv.refl ℝ _)

theorem startupFullCircle_planar (covariant : StartupL2 3) :
    originalValueKernel planarPartMap (originalCircleKernel covariant) =
      originalValueKernel planarPartMap covariant -
        originalTangentialKernel (originalValueKernel planarPartMap covariant) := by
  have planar (field : StartupL2 2) : originalValueKernel planarPartMap (originalValueKernel planarInclusionMap field) = field := by
    change ((originalValueKernel planarPartMap).comp (originalValueKernel planarInclusionMap)) field = _
    rw [originalValueKernel_comp, planarPart_planarInclusion, originalValueKernel_id]
    rfl
  have scalar (field : StartupL2 1) : originalValueKernel planarPartMap (originalValueKernel toroidalInclusionMap field) = 0 := by
    change ((originalValueKernel planarPartMap).comp (originalValueKernel toroidalInclusionMap)) field = _
    rw [originalValueKernel_comp, planarPart_toroidalInclusion, originalValueKernel_zero]
    rfl
  change originalValueKernel planarPartMap (covariant -
    (originalValueKernel planarInclusionMap (originalTangentialKernel (originalValueKernel planarPartMap covariant)) +
      originalValueKernel toroidalInclusionMap (startupCharacterKernel 1 0 (originalValueKernel toroidalPartMap covariant)))) = _
  rw [map_sub, map_add, planar, scalar, add_zero]

theorem startupFullCircle_scalar (covariant : StartupL2 3) :
    originalValueKernel toroidalPartMap (originalCircleKernel covariant) =
      originalValueKernel toroidalPartMap covariant -
        startupCharacterKernel 1 0 (originalValueKernel toroidalPartMap covariant) := by
  have planar (field : StartupL2 2) : originalValueKernel toroidalPartMap (originalValueKernel planarInclusionMap field) = 0 := by
    change ((originalValueKernel toroidalPartMap).comp (originalValueKernel planarInclusionMap)) field = _
    rw [originalValueKernel_comp, toroidalPart_planarInclusion, originalValueKernel_zero]
    rfl
  have scalar (field : StartupL2 1) : originalValueKernel toroidalPartMap (originalValueKernel toroidalInclusionMap field) = field := by
    change ((originalValueKernel toroidalPartMap).comp (originalValueKernel toroidalInclusionMap)) field = _
    rw [originalValueKernel_comp, toroidalPart_toroidalInclusion, originalValueKernel_id]
    rfl
  change originalValueKernel toroidalPartMap (covariant -
    (originalValueKernel planarInclusionMap (originalTangentialKernel (originalValueKernel planarPartMap covariant)) +
      originalValueKernel toroidalInclusionMap (startupCharacterKernel 1 0 (originalValueKernel toroidalPartMap covariant)))) = _
  rw [map_sub, map_add, planar, scalar, zero_add]

/-- Shared actual rough-force boundary. The scalar is literally Kpsi, the
full three-component unknown is literally Q0 a_C, and its weak gradient is
recovered from the genuine original Qrad row. No H1, smooth-core, unprojected
force equation, or zero vector-average assumption is supplied by the caller. -/
theorem startupSame_fullCircle_force_consumer (psi : StartupL2 1) (covariant : StartupL2 3) (right : StartupL2 2)
    (projected : StartupWeakProjectedForceEquation psi (originalValueKernel planarPartMap covariant) right)
    (rawPsi : ℤ → Spatial → PhysicalValue 1)
    (samePsi : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ, psi point cell = rawPsi cell point)
    (psiOrbitMean : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (∫ angle in Icc (0 : ℝ) (2*Real.pi), rawPsi cell (planeRotationEquiv angle point)) = 0) :
    StartupWeakForceEquation (originalScalarInverseKernel psi)
      (originalValueKernel planarPartMap (originalCircleKernel covariant)) right ∧
    (∀ cell test, startupCoordinateTestPairing cell 0 (startupMeanTest test) (originalScalarInverseKernel psi) = 0) ∧
    (∀ cell coordinate test,
      -startupCoordinateTestPairing cell 0 (startupDerivativeTest coordinate test) (originalScalarInverseKernel psi) =
        startupCoordinateTestPairing cell coordinate test
          (startupRecoveredGradient (originalValueKernel planarPartMap (originalCircleKernel covariant)) right)) := by
  have mean := startupScalarWeakMean_of_rawOrbit psi rawPsi samePsi psiOrbitMean
  have rows := startupSame_projected_scalarPrimitive_force psi (originalValueKernel planarPartMap covariant) right projected mean
  rw [← startupFullCircle_planar covariant] at rows
  exact ⟨rows.1, rows.2, startupSame_weakGradient _ _ _ rows.1 rows.2⟩

end Grad.CartesianStartup
