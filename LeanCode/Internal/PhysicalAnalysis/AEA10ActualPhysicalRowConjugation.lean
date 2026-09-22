import AEA9PhysicalBalancingDerivative
import AEA8ActualNormalizedLowHilbertAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularLowReference
open Grad.AnnularLowEnergy Grad.AnnularVariational Grad.PhaseAlgebra
open Grad.CartesianState

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def lowPhysicalWeightedField (parameters : PhaseParameters) (length : ℝ) (mode : LowAnnularMode)
    (entry : Fin 2) (field : ℝ → E) (radius : ℝ) : E :=
  lowPhysicalFactor parameters length radius (entry, mode) • field radius

def lowPhysicalNormalizedForcing (parameters : PhaseParameters) (length radius : ℝ)
    (mode : LowAnnularMode) (entry : Fin 2) (forcing : E) : E :=
  (lowPhysicalFactor parameters length radius (entry, mode) / lowMu length radius mode.val.2) • forcing

theorem lowPhysicalNormalizedForcing_mu (parameters : PhaseParameters) (length radius : ℝ)
    (mode : LowAnnularMode) (positive : 0 < radius) (entry : Fin 2) (forcing : E) :
    lowMu length radius mode.val.2 • lowPhysicalNormalizedForcing parameters length radius mode entry forcing =
      lowPhysicalFactor parameters length radius (entry, mode) • forcing := by
  rw [lowPhysicalNormalizedForcing, smul_smul]
  congr 1
  field_simp [(lowMu_pos length radius mode.val.2 positive).ne']

theorem lowConjugatedFirst_formula (parameters : PhaseParameters) (length radius : ℝ)
    (mode : LowAnnularMode) (positive : 0 < radius) (xi flux : E) :
    lowReferenceFirst parameters length radius mode
      (lowPhysicalFactor parameters length radius (0, mode) • xi)
      (lowPhysicalFactor parameters length radius (1, mode) • flux) =
    lowPhysicalFactor parameters length radius (0, mode) •
      (lowCircularMatrix length radius mode 0 0 • xi + lowCircularMatrix length radius mode 0 1 • flux) +
    (lowPhysicalFactor parameters length radius (0, mode) * lowBalancingLogSlope parameters length radius mode 0) • xi := by
  rw [lowReferenceFirst_matrix, smul_smul, smul_smul,
    lowReferenceMatrix_physical_factor parameters length radius mode positive 0 0,
    lowReferenceMatrix_physical_factor parameters length radius mode positive 0 1]
  norm_num only [show (0 : Fin 2) ≠ 1 from by decide, ↓reduceIte]
  simp only [if_true, if_false]
  module

theorem lowConjugatedSecond_formula (parameters : PhaseParameters) (length radius : ℝ)
    (mode : LowAnnularMode) (positive : 0 < radius) (xi flux : E) :
    lowReferenceSecond parameters length radius mode
      (lowPhysicalFactor parameters length radius (0, mode) • xi)
      (lowPhysicalFactor parameters length radius (1, mode) • flux) =
    lowPhysicalFactor parameters length radius (1, mode) •
      (lowCircularMatrix length radius mode 1 0 • xi + lowCircularMatrix length radius mode 1 1 • flux) +
    (lowPhysicalFactor parameters length radius (1, mode) * lowBalancingLogSlope parameters length radius mode 1) • flux := by
  rw [lowReferenceSecond_matrix, smul_smul, smul_smul,
    lowReferenceMatrix_physical_factor parameters length radius mode positive 1 0,
    lowReferenceMatrix_physical_factor parameters length radius mode positive 1 1]
  norm_num only [show (1 : Fin 2) ≠ 0 from by decide, ↓reduceIte]
  simp only [if_true, if_false]
  module

/-- The exact first physical circular row differentiates to the first BE10 row,
with its source transported by the actual multiplier. -/
theorem lowCircularFirst_hasDerivAt_conjugate (parameters : PhaseParameters) (length radius : ℝ)
    (mode : LowAnnularMode) (positive : 0 < radius) (xi flux : ℝ → E) (forcing : E)
    (physical : HasDerivAt xi (lowCircularMatrix length radius mode 0 0 • xi radius +
      lowCircularMatrix length radius mode 0 1 • flux radius + forcing) radius) :
    HasDerivAt (lowPhysicalWeightedField parameters length mode 0 xi)
      (lowReferenceFirst parameters length radius mode
        (lowPhysicalWeightedField parameters length mode 0 xi radius)
        (lowPhysicalWeightedField parameters length mode 1 flux radius) +
      lowMu length radius mode.val.2 • lowPhysicalNormalizedForcing parameters length radius mode 0 forcing) radius := by
  have derivative := (lowPhysicalFactor_hasDerivAt parameters length radius mode positive 0).smul physical
  have equality : lowReferenceFirst parameters length radius mode
      (lowPhysicalWeightedField parameters length mode 0 xi radius)
      (lowPhysicalWeightedField parameters length mode 1 flux radius) +
      lowMu length radius mode.val.2 • lowPhysicalNormalizedForcing parameters length radius mode 0 forcing =
    (lowPhysicalFactor parameters length radius (0, mode) * lowBalancingLogSlope parameters length radius mode 0) • xi radius +
      lowPhysicalFactor parameters length radius (0, mode) •
        (lowCircularMatrix length radius mode 0 0 • xi radius + lowCircularMatrix length radius mode 0 1 • flux radius + forcing) := by
    unfold lowPhysicalWeightedField
    rw [lowConjugatedFirst_formula parameters length radius mode positive, lowPhysicalNormalizedForcing_mu parameters length radius mode positive]
    module
  have functionEquality : ((fun point => lowPhysicalFactor parameters length point (0, mode)) • xi) =
      lowPhysicalWeightedField parameters length mode 0 xi := by
    funext point
    rfl
  rw [functionEquality] at derivative
  rw [equality]
  simpa only [add_comm] using derivative

/-- The physical corrected-flux row is transported with the same phase and
with mu F, including its exact source normalization. -/
theorem lowCircularSecond_hasDerivAt_conjugate (parameters : PhaseParameters) (length radius : ℝ)
    (mode : LowAnnularMode) (positive : 0 < radius) (xi flux : ℝ → E) (forcing : E)
    (physical : HasDerivAt flux (lowCircularMatrix length radius mode 1 0 • xi radius +
      lowCircularMatrix length radius mode 1 1 • flux radius + forcing) radius) :
    HasDerivAt (lowPhysicalWeightedField parameters length mode 1 flux)
      (lowReferenceSecond parameters length radius mode
        (lowPhysicalWeightedField parameters length mode 0 xi radius)
        (lowPhysicalWeightedField parameters length mode 1 flux radius) +
      lowMu length radius mode.val.2 • lowPhysicalNormalizedForcing parameters length radius mode 1 forcing) radius := by
  have derivative := (lowPhysicalFactor_hasDerivAt parameters length radius mode positive 1).smul physical
  have equality : lowReferenceSecond parameters length radius mode
      (lowPhysicalWeightedField parameters length mode 0 xi radius)
      (lowPhysicalWeightedField parameters length mode 1 flux radius) +
      lowMu length radius mode.val.2 • lowPhysicalNormalizedForcing parameters length radius mode 1 forcing =
    (lowPhysicalFactor parameters length radius (1, mode) * lowBalancingLogSlope parameters length radius mode 1) • flux radius +
      lowPhysicalFactor parameters length radius (1, mode) •
        (lowCircularMatrix length radius mode 1 0 • xi radius + lowCircularMatrix length radius mode 1 1 • flux radius + forcing) := by
    unfold lowPhysicalWeightedField
    rw [lowConjugatedSecond_formula parameters length radius mode positive, lowPhysicalNormalizedForcing_mu parameters length radius mode positive]
    module
  have functionEquality : ((fun point => lowPhysicalFactor parameters length point (1, mode)) • flux) =
      lowPhysicalWeightedField parameters length mode 1 flux := by
    funext point
    rfl
  rw [functionEquality] at derivative
  rw [equality]
  simpa only [add_comm] using derivative

end Hilbert
end Grad.AnnularLowReference
