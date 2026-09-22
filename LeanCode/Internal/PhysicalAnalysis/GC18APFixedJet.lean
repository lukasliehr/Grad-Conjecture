import GC18APAngular
import GC18APJetBounds
import GC18RangeInverse

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra

theorem apValueMap_bound {input output grade : ℕ} (L sigma gamma ell : ℝ)
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output) :
    APJetBound L sigma gamma ell grade (valueMapJetLinear input output mapping) ‖mapping‖ :=
  fun cell field => apValueMap_row_bound L sigma gamma ell cell mapping field

theorem apAverage_bound (L sigma gamma ell : ℝ) (grade : ℕ) :
    APJetBound L sigma gamma ell grade equivariantAverageLinear (averageGradeConstant grade) := by
  have first := (apValueMap_bound (grade := grade) L sigma gamma ell positiveHelicity).comp (norm_nonneg _)
    (show APJetBound L sigma gamma ell grade (angularClosedJetLinear 2 1) (orthogonalGradeConstant grade) from
      fun cell field => apAngular_row_bound L sigma gamma ell cell 1 field)
  have second := (apValueMap_bound (grade := grade) L sigma gamma ell negativeHelicity).comp (norm_nonneg _)
    (show APJetBound L sigma gamma ell grade (angularClosedJetLinear 2 (-1)) (orthogonalGradeConstant grade) from
      fun cell field => apAngular_row_bound L sigma gamma ell cell (-1) field)
  convert first.add second using 1
  · rfl
  · unfold averageGradeConstant
    ring

theorem apTangential_bound (L sigma gamma ell : ℝ) (grade : ℕ) :
    APJetBound L sigma gamma ell grade tangentialJetLinear (tangentialGradeConstant grade) := by
  have reflected := (apValueMap_bound (grade := grade) L sigma gamma ell reflectionValueMap).comp (norm_nonneg _)
    (show APJetBound L sigma gamma ell grade (orthogonalJetLinear 2 cartesianReflectionEquiv) (orthogonalGradeConstant grade) from
      fun cell field => apOrthogonal_row_bound L sigma gamma ell cell cartesianReflectionEquiv field)
  have identity : APJetBound L sigma gamma ell grade (LinearMap.id : ClosedJet 2 →ₗ[ℂ] ClosedJet 2) 1 := by
    intro cell field
    exact (one_mul _).symm.le
  have bound := ((identity.sub reflected).comp
    (add_nonneg zero_le_one (mul_nonneg (norm_nonneg _) (orthogonalGradeConstant_nonnegative grade)))
    (apAverage_bound L sigma gamma ell grade)).smul (1 / 2 : ℂ)
  convert bound using 1
  · rfl
  · unfold tangentialGradeConstant
    norm_num
    ring

def fixedComplementJet : ClosedJet 3 →ₗ[ℂ] ClosedJet 3 :=
  (valueMapJetLinear 2 3 planarInclusionMap).comp
    (tangentialJetLinear.comp (valueMapJetLinear 3 2 planarPartMap)) +
  (valueMapJetLinear 1 3 toroidalInclusionMap).comp
    ((angularClosedJetLinear 1 0).comp (valueMapJetLinear 3 1 toroidalPartMap))

theorem fixedComplementJet_value (field : ClosedJet 3) (point : ClosedDisk) :
    (fixedComplementJet field).value point = cartesianComplementValue field.value point := by
  change (valueMapJet planarInclusionMap (tangentialJet (valueMapJet planarPartMap field)) +
    valueMapJet toroidalInclusionMap (angularClosedJet 0 (valueMapJet toroidalPartMap field))).value point = _
  rw [closedJet_value_add, ContinuousMap.add_apply, valueMapJet_value, valueMapJet_value]
  unfold cartesianComplementValue
  have first : (fun other => planarPartMap (field.value other)) = (valueMapJet planarPartMap field).value :=
    funext (fun other => (valueMapJet_value _ _ other).symm)
  have second : (fun other => toroidalPartMap (field.value other)) = (valueMapJet toroidalPartMap field).value :=
    funext (fun other => (valueMapJet_value _ _ other).symm)
  rw [first, second, closedTangentialValue_jet, closedCharacterProjection_jet]

theorem fixedComplementJet_idempotent (field : ClosedJet 3) :
    fixedComplementJet (fixedComplementJet field) = fixedComplementJet field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [fixedComplementJet_value, fixedComplementJet_value]
  have equality : ⇑(fixedComplementJet field).value = cartesianComplementValue field.value :=
    funext (fixedComplementJet_value field)
  rw [equality]
  exact cartesianComplementValue_idempotent field.value field.value.continuous point

def apComplementConstant (grade : ℕ) : ℝ :=
  ‖planarInclusionMap‖ * (tangentialGradeConstant grade * ‖planarPartMap‖) +
    ‖toroidalInclusionMap‖ * (orthogonalGradeConstant grade * ‖toroidalPartMap‖)

theorem apComplementConstant_nonnegative (grade : ℕ) : 0 ≤ apComplementConstant grade := by
  have tangent := tangentialGradeConstant_nonnegative grade
  have orthogonal := orthogonalGradeConstant_nonnegative grade
  unfold apComplementConstant
  positivity

theorem apFixedComplement_bound (L sigma gamma ell : ℝ) (grade : ℕ) :
    APJetBound L sigma gamma ell grade fixedComplementJet (apComplementConstant grade) := by
  exact ((apValueMap_bound L sigma gamma ell planarInclusionMap).comp (norm_nonneg _)
    ((apTangential_bound L sigma gamma ell grade).comp (tangentialGradeConstant_nonnegative grade)
      (apValueMap_bound L sigma gamma ell planarPartMap))).add
    ((apValueMap_bound L sigma gamma ell toroidalInclusionMap).comp (norm_nonneg _)
      ((show APJetBound L sigma gamma ell grade (angularClosedJetLinear 1 0) (orthogonalGradeConstant grade) from
        fun cell field => apAngular_row_bound L sigma gamma ell cell 0 field).comp
          (orthogonalGradeConstant_nonnegative grade) (apValueMap_bound L sigma gamma ell toroidalPartMap)))

end Grad.GaugeCoefficients.Physical.RadialLedger
