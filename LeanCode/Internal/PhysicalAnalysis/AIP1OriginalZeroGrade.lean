import ANH11DiskL2Density
import QuotientConstantFields
import COR13Maps

noncomputable section
open scoped BigOperators

namespace Grad.InteriorPeriodization
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak
open Grad.NonlinearQuotientBounds

/-- The actual original analytic core with its phase removed at cell zero.
The phase parameters remain arbitrary and are never specialized to zero. -/
def normalizedSingleCore (parameters : PhaseParameters) : ClosedJet 1 →ₗ[ℂ] ACore parameters 1 where
  toFun field := singletonCore parameters (phaseInverseWeightedJet parameters 0 field)
  map_add' first second := by
    apply Subtype.ext
    funext cell
    by_cases zero : cell = 0
    · simp [singletonCore, zero, phaseInverseWeightedJet_add]
    · simp [singletonCore, zero]
  map_smul' scalar field := by
    apply Subtype.ext
    funext cell
    by_cases zero : cell = 0
    · simp [singletonCore, zero, phaseInverseWeightedJet_complex_smul]
    · simp [singletonCore, zero]

def originalZeroCore (parameters : PhaseParameters) : ClosedJet 1 →ₗ[ℂ] GradeCore parameters 1 0 :=
  GradeCore.ofCoreLinear.comp (normalizedSingleCore parameters)

private theorem zeroRow_norm (parameters : PhaseParameters) (field : ClosedJet 1) :
    ‖cellGradeRowLinear (grade := 0) parameters 0
      (phaseInverseWeightedJet parameters 0 field)‖ = ‖closedL2Core field‖ := by
  have indexUnique : ∀ index : GradeMultiIndex 0, index = zeroGradeIndex 0 := by
    intro index
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> omega
  have squared := cellGradeRow_norm_sq (grade := 0) parameters 0
    (phaseInverseWeightedJet parameters 0 field)
  have sum : (∑ index : GradeMultiIndex 0,
      cellFrequency 0 ^ (2 * (0 - cartesianOrder index.toCartesian)) *
        ‖closedContinuousToDiskL2
          (closedMultiDerivative (phaseWeightedJet parameters 0
            (phaseInverseWeightedJet parameters 0 field)) index.toCartesian)‖ ^ 2) =
      ‖closedL2Core field‖ ^ 2 := by
    rw [Finset.sum_eq_single (zeroGradeIndex 0)]
    · simp only [Nat.zero_sub, mul_zero, pow_zero, one_mul,
        phaseWeightedJet_inverse_left, closedMultiDerivative_zeroGradeIndex]
      rfl
    · intro index _ different
      exact (different (indexUnique index)).elim
    · simp
  nlinarith [squared.trans sum, norm_nonneg
    (cellGradeRowLinear (grade := 0) parameters 0 (phaseInverseWeightedJet parameters 0 field)),
    norm_nonneg (closedL2Core field)]

/-- At grade zero, literal original M2 is exactly ordinary disk area L2
after conjugating by the unchanged original phase. -/
theorem originalZeroCore_norm (parameters : PhaseParameters) (field : ClosedJet 1) :
    ‖originalZeroCore parameters field‖ = ‖closedL2Core field‖ := by
  rw [gradeCore_norm_eq_cartesianGradeSeminorm, cartesianGradeSeminorm_apply,
    gradeCoreCoordinates_apply]
  have coordinates : cartesianGradeCoordinates parameters 0
      (normalizedSingleCore parameters field) =
      lp.single (E := fun _ : ℤ => CartesianGradeRow 1 0) 2 0 (cellGradeRowLinear (grade := 0) parameters 0
        (phaseInverseWeightedJet parameters 0 field)) := by
    apply Subtype.ext
    funext cell
    by_cases zero : cell = 0
    · subst cell
      simp [cartesianGradeCoordinates, rawCartesianGradeCoordinates,
        normalizedSingleCore, singletonCore]
    · simp [cartesianGradeCoordinates, rawCartesianGradeCoordinates,
        normalizedSingleCore, singletonCore, zero]
  change ‖cartesianGradeCoordinates parameters 0 (normalizedSingleCore parameters field)‖ = _
  rw [coordinates, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
  exact zeroRow_norm parameters field

end Grad.InteriorPeriodization
