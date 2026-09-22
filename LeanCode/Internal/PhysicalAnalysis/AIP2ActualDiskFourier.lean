import AIP1OriginalZeroGrade
import GC20RangeExtension

noncomputable section

namespace Grad.InteriorPeriodization
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.FourierGrade Grad.COR12Extension Grad.COR13Completion

local instance originalGradeReal (parameters : PhaseParameters) :
    NormedSpace ℝ (AGrade parameters 1 0) :=
  (InnerProductSpace.rclikeToReal ℂ (AGrade parameters 1 0)).toNormedSpace

def originalZeroCoreInto (parameters : PhaseParameters) : ClosedJet 1 →ₗ[ℂ] AGrade parameters 1 0 :=
  (aGradeEta parameters).toLinearMap.comp (originalZeroCore parameters)

theorem originalZeroCoreInto_norm (parameters : PhaseParameters) (field : ClosedJet 1) :
    ‖originalZeroCoreInto parameters field‖ = ‖closedL2Core field‖ := by
  change ‖aGradeEta parameters (originalZeroCore parameters field)‖ = _
  rw [aGradeEta_norm, originalZeroCore_norm]

theorem diskOriginalZero_exists (parameters : PhaseParameters) :
    ∃ insertion : DiskL2 1 →L[ℝ] AGrade parameters 1 0,
      (∀ core, insertion (closedL2Core core) = originalZeroCoreInto parameters core) ∧
      (∀ field, ‖insertion field‖ ≤ ‖field‖) := by
  let embed := closedL2Core.restrictScalars ℝ
  have extension := collarRange_extension embed
    ((originalZeroCoreInto parameters).restrictScalars ℝ) 1 (by norm_num)
    (fun core => by
      change ‖originalZeroCoreInto parameters core‖ ≤ 1 * ‖closedL2Core core‖
      rw [one_mul]
      exact (originalZeroCoreInto_norm parameters core).le)
  obtain ⟨extended, coreLaw, bound⟩ := extension
  let inclusion : DiskL2 1 →L[ℝ] (LinearMap.range embed).topologicalClosure :=
    (ContinuousLinearMap.id ℝ _).codRestrict _ (fun field => closedL2Core_denseRange field)
  refine ⟨extended.comp inclusion, coreLaw, ?_⟩
  intro field
  exact (bound (inclusion field)).trans_eq (one_mul ‖field‖)

/-- Ordinary disk L2 inserted into the exact original grade-zero completion,
with the unchanged phase conjugation built into its dense core. -/
def diskOriginalZero (parameters : PhaseParameters) : DiskL2 1 →L[ℝ] AGrade parameters 1 0 :=
  (diskOriginalZero_exists parameters).choose

theorem diskOriginalZero_core (parameters : PhaseParameters) (core : ClosedJet 1) :
    diskOriginalZero parameters (closedL2Core core) = originalZeroCoreInto parameters core :=
  (diskOriginalZero_exists parameters).choose_spec.1 core

theorem diskOriginalZero_norm (parameters : PhaseParameters) (field : DiskL2 1) :
    ‖diskOriginalZero parameters field‖ = ‖field‖ := by
  apply isClosed_property closedL2Core_denseRange
    (isClosed_eq (continuous_norm.comp (diskOriginalZero parameters).continuous) continuous_norm) _ field
  intro core
  change ‖diskOriginalZero parameters (closedL2Core core)‖ = ‖closedL2Core core‖
  rw [diskOriginalZero_core, originalZeroCoreInto_norm]

/-- The accepted physical Fourier extension applied to the actual disk L2
class, without introducing independent Fourier coefficients. -/
def diskFourier (parameters : PhaseParameters) : DiskL2 1 →L[ℝ] JGrade (ComplexEuclidean 1) 0 :=
  ((completedExtension parameters).restrictScalars ℝ).comp (diskOriginalZero parameters)

theorem diskFourier_core (parameters : PhaseParameters) (core : ClosedJet 1) :
    diskFourier parameters (closedL2Core core) =
      coreToGrade 0 (weightedFourierExtension parameters (normalizedSingleCore parameters core)) := by
  change completedExtension parameters (diskOriginalZero parameters (closedL2Core core)) = _
  rw [diskOriginalZero_core]
  exact completedExtension_apply_eta parameters (originalZeroCore parameters core)

theorem diskFourier_bound (parameters : PhaseParameters) (field : DiskL2 1) :
    ‖diskFourier parameters field‖ ≤ sameGradeConstant 0 * ‖field‖ := by
  exact ((completedExtension parameters).le_opNorm (diskOriginalZero parameters field)).trans
    ((mul_le_mul_of_nonneg_right (completedExtension_norm_le parameters) (norm_nonneg _)).trans_eq
      (congrArg (sameGradeConstant 0 * ·) (diskOriginalZero_norm parameters field)))

end Grad.InteriorPeriodization
