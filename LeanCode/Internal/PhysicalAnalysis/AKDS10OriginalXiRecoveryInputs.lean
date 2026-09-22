import AKDP33OriginalCircleRadialNorm
import AKDS8ActualNativeXiWeakRecoveryBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.CartesianStartup Grad.PDEBootstrap Grad.GenericCarriers
open Grad.NonlinearProduct Grad.NonlinearQuotientBounds Grad.Constraints Grad.Constraints.Gauges
open Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.RadialLedger

/-- SAME original circle and genuine Qrad projections supply both inputs
of scalar recovery with fixed same-grade constants and no derivative loss. -/
theorem originalXiRecoveryInputs (parameters : PhaseParameters)
    (covariant force : ACore parameters 3) (known : ACore parameters 2) :
    ∃ vector right : ACore parameters 2,
      originalSourceFieldLinear parameters vector =
        originalValueKernel planarPartMap (originalCircleKernel (originalSourceFieldLinear parameters covariant)) ∧
      originalSourceFieldLinear parameters right =
        startupGenuineQradKernel (originalSourceFieldLinear parameters known) -
          (2:ℂ) • startupGenuineQradKernel
            (originalValueKernel planarPartMap (originalSourceFieldLinear parameters force)) ∧
      ∀ grade,
        originalGradeNorm grade vector ≤
          (‖planarPartMap‖*(startupOriginalCircle_core_bound parameters grade).choose)*originalGradeNorm grade covariant ∧
        originalGradeNorm grade right ≤ (startupOriginalQrad_core_bound parameters grade).choose *
          (originalGradeNorm grade known+2*‖planarPartMap‖*originalGradeNorm grade force) := by
  obtain ⟨circle,circleSame⟩ := startupOriginalCircle_core_exists parameters covariant
  obtain ⟨knownImage,knownSame⟩ := startupOriginalQrad_core_exists parameters known
  obtain ⟨forceImage,forceSame⟩ := startupOriginalQrad_core_exists parameters (valueMapCore parameters planarPartMap force)
  let vector := valueMapCore parameters planarPartMap circle
  let right := knownImage-(2:ℂ) • forceImage
  refine ⟨vector,right,?_,?_,?_⟩
  · change originalSourceFieldLinear parameters (valueMapCore parameters planarPartMap circle) = _
    rw [originalSourceFieldLinear_valueMap,circleSame]
  · change originalSourceFieldLinear parameters (knownImage-(2:ℂ) • forceImage) = _
    rw [map_sub,map_smul,knownSame,forceSame,originalSourceFieldLinear_valueMap]
  intro grade
  have circleBound := (startupOriginalCircle_core_bound parameters grade).choose_spec.2 covariant circle circleSame
  have knownBound := (startupOriginalQrad_core_bound parameters grade).choose_spec.2 known knownImage knownSame
  have forceBound := (startupOriginalQrad_core_bound parameters grade).choose_spec.2
    (valueMapCore parameters planarPartMap force) forceImage forceSame
  constructor
  · exact (valueMapCore_bound planarPartMap circle grade).trans
      ((mul_le_mul_of_nonneg_left circleBound (norm_nonneg _)).trans_eq (by ring))
  · have forcePaid := forceBound.trans (mul_le_mul_of_nonneg_left
        (valueMapCore_bound planarPartMap force grade)
        (startupOriginalQrad_core_bound parameters grade).choose_spec.1)
    have twice : originalGradeNorm grade ((2:ℂ) • forceImage) = 2*originalGradeNorm grade forceImage := by
      rw [originalGradeNorm_smul]
      norm_num
    exact (originalGradeNorm_sub_le grade knownImage ((2:ℂ) • forceImage)).trans
      ((add_le_add knownBound (twice.le.trans (mul_le_mul_of_nonneg_left forcePaid (by norm_num)))).trans_eq (by ring))

end Grad.OriginalCoreRealization
