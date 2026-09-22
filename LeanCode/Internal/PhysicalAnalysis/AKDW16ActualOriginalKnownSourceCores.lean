import AKDW14FixedOriginalCoreNorm
import AKN16OriginalFlatSourcePrimitives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.OriginalCoreRealization Grad.ActualOriginalSourceMoments Grad.FlatSourceProjection Grad.QuotientProjection
open Grad.ExhaustionSourceAllocation Grad.GaugeCoefficients.Physical.RadialLedger

def startupOriginalKnownForceCore (parameters : PhaseParameters) (source : SmoothQuotient parameters) : ACore parameters 2 :=
  (startupOriginalQrad_core_exists parameters (cartesianSourceVector source)).choose

theorem startupOriginalKnownForceCore_same (parameters : PhaseParameters) (source : SmoothQuotient parameters) :
    originalSourceFieldLinear parameters (startupOriginalKnownForceCore parameters source)=
      startupGenuineQradKernel (originalSourceFieldLinear parameters (cartesianSourceVector source)) :=
  (startupOriginalQrad_core_exists parameters (cartesianSourceVector source)).choose_spec

/-- The literal source projector has a same-grade original-width bound. -/
theorem startupOriginalKnownForceCore_bound (parameters : PhaseParameters) (rank : ℕ) :
    ∃ constant : ℝ,0≤constant ∧ ∀ source : SmoothQuotient parameters,
      originalGradeNorm rank (startupOriginalKnownForceCore parameters source)≤constant*‖quotientEta parameters rank source‖ := by
  obtain ⟨constant,nonnegative,bounded⟩ := startupOriginalQrad_core_bound parameters rank
  refine ⟨constant,nonnegative,fun source => ?_⟩
  exact (bounded (cartesianSourceVector source) (startupOriginalKnownForceCore parameters source)
    (startupOriginalKnownForceCore_same parameters source)).trans
    (mul_le_mul_of_nonneg_left (originalPlanarCore_norm_le parameters rank source) nonnegative)

/-- At original unit scale both scalar known rows retain the physical L^-1. -/
def startupOriginalKnownScalarCore (parameters : PhaseParameters) (length : ℝ)
    (source : SmoothQuotient parameters) (row : Fin 4) : ACore parameters 1 := (length : ℂ)⁻¹ • source row

theorem startupOriginalKnownScalarCore_same (parameters : PhaseParameters) (length : ℝ)
    (source : SmoothQuotient parameters) (row : Fin 4) :
    originalSourceFieldLinear parameters (startupOriginalKnownScalarCore parameters length source row)=
      (length : ℂ)⁻¹ • originalSourceFieldLinear parameters (source row) := by
  rw [startupOriginalKnownScalarCore,map_smul]

theorem startupOriginalKnownScalarCore_bound (parameters : PhaseParameters) (length : ℝ)
    (rank : ℕ) (source : SmoothQuotient parameters) (row : Fin 4) :
    originalGradeNorm rank (startupOriginalKnownScalarCore parameters length source row)≤
      ‖(length : ℂ)⁻¹‖*‖quotientEta parameters rank source‖ := by
  rw [startupOriginalKnownScalarCore,originalGradeNorm_smul]
  exact mul_le_mul_of_nonneg_left (originalScalarCore_norm_le parameters rank source row) (norm_nonneg _)

end Grad.CartesianStartup
