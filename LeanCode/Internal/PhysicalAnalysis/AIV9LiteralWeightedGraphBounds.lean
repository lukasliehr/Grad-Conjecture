import AIV8ExactOriginalHighConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularOriginalHigh
open Grad.AnnularVariational Grad.AnnularFluxTrace Grad.AnnularOmegaGraph Grad.AnnularHighTilt Grad.AnnularGrades

variable (lower length : ℝ) (positive : 0 < lower) (strict : lower < 1)
  (lengthPositive : 0 < length) (angular cell inserted : ℕ)

def originalNuWeighted (field : originalNuGraph lower positive)
    (grade : HasAnnularFluxGrade lower positive angular cell inserted (originalNuPairEquivalence lower positive field)) :
    originalNuGraph lower positive :=
  (originalNuPairEquivalence lower positive).symm
    (annularFluxGraphWeighted lower positive angular cell inserted
      (originalNuPairEquivalence lower positive field) grade)

theorem originalNuDecode_weighted (field : originalNuGraph lower positive)
    (grade : HasAnnularFluxGrade lower positive angular cell inserted (originalNuPairEquivalence lower positive field)) :
    originalNuDecode lower positive angular cell inserted
      (originalNuWeighted lower positive angular cell inserted field grade) = field := by
  apply (originalNuPairEquivalence lower positive).injective
  rw [originalNuDecode_pair]
  change annularFluxGraphDecode lower positive angular cell inserted
    ((originalNuPairEquivalence lower positive) ((originalNuPairEquivalence lower positive).symm _)) = _
  rw [(originalNuPairEquivalence lower positive).apply_symm_apply]
  exact annularFluxGraphDecode_weighted lower positive angular cell inserted _ grade

/-- Multiplication by every original grade commutes with the SAME actual
radial transformation, including its constrained derivative coordinate. -/
theorem originalFluxTilt_weighted (field : originalNuGraph lower positive)
    (grade : HasAnnularFluxGrade lower positive angular cell inserted (originalNuPairEquivalence lower positive field))
    (outputGrade : HasAnnularOmegaGrade lower angular cell inserted
      (originalFluxTiltEquivalence lower length positive strict.le lengthPositive field).val) :
    originalFluxTiltEquivalence lower length positive strict.le lengthPositive
      (originalNuWeighted lower positive angular cell inserted field grade) =
    annularOmegaWeightedGraph lower length positive lengthPositive angular cell inserted
      (originalFluxTiltEquivalence lower length positive strict.le lengthPositive field) outputGrade := by
  apply annularOmegaGraphDecode_injective lower length positive lengthPositive angular cell inserted
  rw [← originalFluxTilt_decode lower length positive strict lengthPositive angular cell inserted,
    originalNuDecode_weighted, annularOmegaGraphDecode_weighted]

theorem originalEnergyTilt_weighted (field : annularEnergySpace lower length positive)
    (grade : HasAnnularEnergyGrade lower length positive angular cell inserted field)
    (outputGrade : HasAnnularEnergyGrade lower length positive angular cell inserted
      (highEnergyWeight lower length positive strict.le field)) :
    highEnergyWeight lower length positive strict.le
      (annularWeightedEnergy lower length positive angular cell inserted field grade) =
    annularWeightedEnergy lower length positive angular cell inserted
      (highEnergyWeight lower length positive strict.le field) outputGrade := by
  apply annularEnergyDecode_injective lower length positive angular cell inserted
  rw [← originalEnergyTilt_decode lower length positive strict angular cell inserted,
    annularEnergyDecode_weighted, annularEnergyDecode_weighted]

/-- Uniform high flux inverse estimate in each literal ORIGINAL inserted
norm. There is no dependence on any of the three grade indices. -/
theorem originalFluxTilt_weighted_inverse_bound (field : originalNuGraph lower positive)
    (grade : HasAnnularFluxGrade lower positive angular cell inserted (originalNuPairEquivalence lower positive field))
    (outputGrade : HasAnnularOmegaGrade lower angular cell inserted
      (originalFluxTiltEquivalence lower length positive strict.le lengthPositive field).val) :
    ‖originalNuWeighted lower positive angular cell inserted field grade‖ ≤
      (2 + length⁻¹ + highTiltExponent) *
        ‖annularOmegaWeightedGraph lower length positive lengthPositive angular cell inserted
          (originalFluxTiltEquivalence lower length positive strict.le lengthPositive field) outputGrade‖ := by
  rw [← originalFluxTilt_weighted lower length positive strict lengthPositive angular cell inserted field grade outputGrade]
  have estimate := originalFluxTilt_inverse_bound lower length positive strict.le lengthPositive
    (originalFluxTiltEquivalence lower length positive strict.le lengthPositive
      (originalNuWeighted lower positive angular cell inserted field grade))
  rwa [(originalFluxTiltEquivalence lower length positive strict.le lengthPositive).symm_apply_apply] at estimate

theorem originalEnergyTilt_weighted_inverse_bound (field : annularEnergySpace lower length positive)
    (grade : HasAnnularEnergyGrade lower length positive angular cell inserted field)
    (outputGrade : HasAnnularEnergyGrade lower length positive angular cell inserted
      (highEnergyWeight lower length positive strict.le field)) :
    ‖annularWeightedEnergy lower length positive angular cell inserted field grade‖ ≤
      3 * ‖annularWeightedEnergy lower length positive angular cell inserted
        (highEnergyWeight lower length positive strict.le field) outputGrade‖ := by
  rw [← originalEnergyTilt_weighted lower length positive strict angular cell inserted field grade outputGrade]
  have estimate := highEnergyUnweight_bound lower length positive strict.le
    (highEnergyWeight lower length positive strict.le
      (annularWeightedEnergy lower length positive angular cell inserted field grade))
  rwa [highEnergy_unweight_weight] at estimate

end Grad.AnnularOriginalHigh
