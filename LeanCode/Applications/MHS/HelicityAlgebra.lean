import PlanarValueMaps

noncomputable section

namespace Grad.Constraints

theorem positiveHelicity_idempotent : positiveHelicity.comp positiveHelicity = positiveHelicity := by
  apply ContinuousLinearMap.ext
  intro value
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [ContinuousLinearMap.comp_apply, positiveHelicity_apply] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem negativeHelicity_idempotent : negativeHelicity.comp negativeHelicity = negativeHelicity := by
  apply ContinuousLinearMap.ext
  intro value
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [ContinuousLinearMap.comp_apply, negativeHelicity_apply] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem positiveHelicity_negative : positiveHelicity.comp negativeHelicity = 0 := by
  apply ContinuousLinearMap.ext
  intro value
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [ContinuousLinearMap.comp_apply, positiveHelicity_apply, negativeHelicity_apply] <;>
      ring_nf <;> simp [Complex.I_sq]

theorem negativeHelicity_positive : negativeHelicity.comp positiveHelicity = 0 := by
  apply ContinuousLinearMap.ext
  intro value
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [ContinuousLinearMap.comp_apply, positiveHelicity_apply, negativeHelicity_apply] <;>
      ring_nf <;> simp [Complex.I_sq]

theorem reflectionValue_positive :
    reflectionValueMap.comp positiveHelicity = negativeHelicity.comp reflectionValueMap := by
  apply ContinuousLinearMap.ext
  intro value
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [ContinuousLinearMap.comp_apply, positiveHelicity_apply, negativeHelicity_apply,
      reflectionValueMap, reflectionValueLinear]
  ring

theorem reflectionValue_negative :
    reflectionValueMap.comp negativeHelicity = positiveHelicity.comp reflectionValueMap := by
  apply ContinuousLinearMap.ext
  intro value
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [ContinuousLinearMap.comp_apply, positiveHelicity_apply, negativeHelicity_apply,
      reflectionValueMap, reflectionValueLinear] <;> ring

end Grad.Constraints
