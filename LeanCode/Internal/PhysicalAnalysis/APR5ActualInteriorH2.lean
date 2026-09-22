import APR4OrdinarySobolevConsumer
import AIP18ActualInteriorBound

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace Grad.OrdinaryDiskReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak
open Grad.FourierGrade Grad.COR12Extension Grad.COR13Completion
open Grad.InteriorPeriodization Grad.NonlinearQuotientBounds

/-- Undoing the actual single-cell inverse-phase normalization recovers the
original disk L2 class, including all nonsmooth completed inputs. -/
theorem originalDisk_actualL2 (parameters : PhaseParameters) (field : DiskL2 1) :
    unitDiskBulk 0 (originalDisk parameters 0 (diskOriginalZero parameters field)) = field := by
  apply isClosed_property closedL2Core_denseRange
    (isClosed_eq ((unitDiskBulk 0).continuous.comp ((originalDisk parameters 0).continuous.comp
      (diskOriginalZero parameters).continuous)) continuous_id) _ field
  intro core
  have phase : phaseZeroCore parameters 0 (originalZeroCore parameters core) = core := by
    change phaseWeightedJet parameters 0 (phaseInverseWeightedJet parameters 0 core) = core
    exact phaseWeightedJet_inverse_left parameters 0 core
  have original := (congrArg (originalDisk parameters 0) (diskOriginalZero_core parameters core)).trans
    ((originalDisk_core parameters 0 (originalZeroCore parameters core)).trans
      (congrArg (unitDiskCoreInto 0) phase))
  exact (congrArg (unitDiskBulk 0) original).trans (unitDiskBulk_core 0 core)

/-- Any higher Fourier representative of the constructed physical disk
extension yields ordinary Sobolev regularity of that very same disk field. -/
theorem fourierDisk_actualL2 (parameters : PhaseParameters) (grade : ℕ)
    (values : JGrade (ComplexEuclidean 1) grade) (field : DiskL2 1)
    (same : inclusion grade 0 (Nat.zero_le grade) values = diskFourier parameters field) :
    unitDiskBulk grade (fourierDisk parameters grade values) = field :=
  (fourierDisk_reconstructs parameters grade values (diskOriginalZero parameters field) same).trans
    (originalDisk_actualL2 parameters field)

def interiorOrdinaryConstant : ℝ := sameGradeConstant 2 * interiorFourierConstant

theorem interiorOrdinaryConstant_nonnegative : 0 ≤ interiorOrdinaryConstant :=
  mul_nonneg (sameGradeConstant_nonnegative 2) interiorFourierConstant_nonnegative

/-- Actual interior H2 regularity of the constructed weak Robin inverse.
The bulk is the literal localizedDiskField, and the uniform polynomial
constant multiplies the original high L2 source norm. No regularity premise. -/
theorem actualInteriorOrdinaryH2 (parameters : PhaseParameters) (parameter : ℝ) (source : highDiskL2) :
    ∃ regular : unitDiskSobolev 2,
      unitDiskBulk 2 regular = localizedDiskField parameter source ∧
      ‖regular‖ ≤ interiorOrdinaryConstant * (1 + parameter ^ 2) * ‖source‖ := by
  obtain ⟨higher, same, bound⟩ := actualInteriorFourier_consumer parameters parameter source
  refine ⟨fourierDisk parameters 2 higher,
    fourierDisk_actualL2 parameters 2 higher (localizedDiskField parameter source) same,
    (fourierDisk_bound parameters 2 higher).trans ?_⟩
  exact (mul_le_mul_of_nonneg_left bound (sameGradeConstant_nonnegative 2)).trans_eq (by
    unfold interiorOrdinaryConstant
    ring)

end Grad.OrdinaryDiskReconstruction
