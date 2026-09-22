import ANG24OrdinarySobolevSource
import COR14Inclusion

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace Grad.OrdinaryDiskReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger

/-- Cell zero retains its actual phase. This is the coefficient after the
original W_gamma conjugation, rather than the original unweighted core. -/
def phaseZeroCore (parameters : PhaseParameters) (grade : ℕ) :
    GradeCore parameters 1 grade →ₗ[ℂ] ClosedJet 1 :=
  (phaseWeightedJetLinear parameters 0).comp ((LinearMap.proj 0).comp
    ((originalCoreSubmodule parameters 1).subtype.comp GradeCore.toCoreLinear))

theorem phaseZeroCore_apply (parameters : PhaseParameters) (grade : ℕ)
    (field : GradeCore parameters 1 grade) :
    phaseZeroCore parameters grade field = phaseWeightedJet parameters 0 (field.toCore.val 0) := rfl

/-- At cell zero lambda_0=1, so the original Cartesian row is precisely the
ordinary disk row of the phase-weighted jet, with each index counted once. -/
theorem phaseZero_row (parameters : PhaseParameters) (grade : ℕ) (field : ClosedJet 1) :
    unitSobolevRow grade (phaseWeightedJet parameters 0 field) =
      cellGradeRowLinear (grade := grade) parameters 0 field := by
  have frequency : cellFrequency (0 : ℤ) = 1 := by
    norm_num [cellFrequency, Grad.CellWeights.cellWeight]
  apply PiLp.ext
  intro index
  rw [unitSobolevRow_coordinate, cellGradeRowLinear_apply, frequency]
  simp only [Complex.ofReal_one, one_pow, one_smul]
  rfl

def originalDiskCore (parameters : PhaseParameters) (grade : ℕ) :
    GradeCore parameters 1 grade →ₗ[ℂ] unitDiskSobolev grade :=
  (unitDiskCoreInto grade).comp (phaseZeroCore parameters grade)

theorem originalDiskCore_bound (parameters : PhaseParameters) (grade : ℕ)
    (field : GradeCore parameters 1 grade) :
    ‖originalDiskCore parameters grade field‖ ≤ 1 * ‖field‖ := by
  change ‖unitDiskCoreInto grade (phaseWeightedJet parameters 0 (field.toCore.val 0))‖ ≤ _
  rw [unitDiskCore_norm, phaseZero_row, one_mul,
    gradeCore_norm_eq_cartesianGradeSeminorm, cartesianGradeSeminorm_apply]
  exact lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
    (gradeCoreCoordinates parameters field) 0

end Grad.OrdinaryDiskReconstruction
