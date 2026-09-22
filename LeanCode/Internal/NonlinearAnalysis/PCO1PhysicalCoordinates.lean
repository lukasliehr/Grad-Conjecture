import TameSeedField
import QR13ValueReality
import GaugeProjectionBounds

noncomputable section

namespace Grad.PhysicalCoordinates

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.NonlinearQuotientBounds Grad.CompletedReality Grad.NonlinearProduct

/-- Explicit transport from gauge storage `(planar₁,planar₂,toroidal)`
to the paper's physical order `(planar₁,toroidal,planar₂)`. -/
def toPhysicalValue : ComplexEuclidean 3 →L[ℂ] ComplexEuclidean 3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun value => WithLp.toLp 2 ![value 0, value 2, value 1]
      map_add' := by
        intro first second
        apply PiLp.ext
        intro coordinate
        fin_cases coordinate <;> simp
      map_smul' := by
        intro scalar value
        apply PiLp.ext
        intro coordinate
        fin_cases coordinate <;> simp }

theorem toPhysicalValue_involutive (value : ComplexEuclidean 3) :
    toPhysicalValue (toPhysicalValue value) = value := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [toPhysicalValue]

theorem toPhysicalValue_norm (value : ComplexEuclidean 3) :
    ‖toPhysicalValue value‖ = ‖value‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2, Fin.sum_univ_three, Fin.sum_univ_three]
  congr 1
  change ‖value 0‖ ^ 2 + ‖value 2‖ ^ 2 + ‖value 1‖ ^ 2 =
    ‖value 0‖ ^ 2 + ‖value 1‖ ^ 2 + ‖value 2‖ ^ 2
  ring

theorem toPhysicalValue_norm_le : ‖toPhysicalValue‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro value
  rw [toPhysicalValue_norm, one_mul]

theorem toPhysicalValue_planar (value : ComplexEuclidean 2) :
    toPhysicalValue (Gauges.planarInclusionMap value) = tamePlanarInclusion value := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [toPhysicalValue, Gauges.planarInclusionMap, tamePlanarInclusion]

theorem toPhysicalValue_toroidal (value : ComplexEuclidean 1) :
    toPhysicalValue (Gauges.toroidalInclusionMap value) = tameTangentInclusion value := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [toPhysicalValue, Gauges.toroidalInclusionMap, tameTangentInclusion]

/-- The same pointwise permutation on every original all-grade cell. -/
def toPhysicalCore (parameters : PhaseParameters) :
    ACore parameters 3 →ₗ[ℂ] ACore parameters 3 :=
  valueMapCore parameters toPhysicalValue

theorem toPhysicalCore_value (parameters : PhaseParameters) (field : ACore parameters 3)
    (cell : ℤ) (point : ClosedDisk) :
    ((toPhysicalCore parameters field).val cell).value point =
      toPhysicalValue ((field.val cell).value point) :=
  valueMapCore_value toPhysicalValue field cell point

theorem toPhysicalCore_involutive (parameters : PhaseParameters) (field : ACore parameters 3) :
    toPhysicalCore parameters (toPhysicalCore parameters field) = field := by
  apply Subtype.ext
  funext cell
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [toPhysicalCore_value, toPhysicalCore_value, toPhysicalValue_involutive]

theorem toPhysicalCore_norm_le (parameters : PhaseParameters) (grade : ℕ)
    (field : ACore parameters 3) :
    originalGradeNorm grade (toPhysicalCore parameters field) ≤ originalGradeNorm grade field :=
  (valueMapCore_bound toPhysicalValue field grade).trans
    (by
      simpa only [one_mul] using (mul_le_mul_of_nonneg_right toPhysicalValue_norm_le
        (originalGradeNorm_nonnegative grade field)))

theorem toPhysicalCore_norm (parameters : PhaseParameters) (grade : ℕ)
    (field : ACore parameters 3) :
    originalGradeNorm grade (toPhysicalCore parameters field) = originalGradeNorm grade field := by
  apply le_antisymm (toPhysicalCore_norm_le parameters grade field)
  have bound := toPhysicalCore_norm_le parameters grade (toPhysicalCore parameters field)
  rwa [toPhysicalCore_involutive] at bound

theorem toPhysicalValue_conjugate :
    operatorConjugation 3 3 toPhysicalValue = toPhysicalValue := by
  apply ContinuousLinearMap.ext
  intro vector
  change cartesianPhysicalConjugation 3
    (toPhysicalValue (cartesianPhysicalConjugation 3 vector)) = _
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [toPhysicalValue, cartesianPhysicalConjugation_apply]

theorem toPhysicalCore_conjugate (parameters : PhaseParameters) (field : ACore parameters 3) :
    cartesianCoreConjugation parameters (toPhysicalCore parameters field) =
      toPhysicalCore parameters (cartesianCoreConjugation parameters field) := by
  change cartesianCoreConjugation parameters (Grad.Constraints.valueMapCore toPhysicalValue parameters field) = _
  rw [valueMapCore_conjugate, toPhysicalValue_conjugate]
  rfl

theorem toPhysicalCore_zeroJets (parameters : PhaseParameters) (field : ACore parameters 3)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (field.val cell)) :
    ∀ cell, ZeroCartesianFirstJets ((toPhysicalCore parameters field).val cell) := by
  intro cell order bounded
  exact valueMapJet_preserves_zero_derivatives toPhysicalValue (field.val cell) (zeroJets cell order bounded)

end Grad.PhysicalCoordinates
