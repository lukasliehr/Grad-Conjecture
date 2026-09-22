import GC10Derivative

noncomputable section

set_option maxHeartbeats 3000000

open Set
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets
open Grad.GaugeCoefficients.Envelope
open scoped BigOperators ContDiff ENNReal Topology

namespace Grad.GaugeCoefficients.Algebra

theorem gradeProductConstant_zero : gradeProductConstant 0 = 1 := by
  unfold gradeProductConstant
  norm_num only [pow_zero, one_mul]
  have indexUnique (index : DerivativeIndex 0) : index = zeroDerivativeIndex := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      omega
    · apply Fin.ext
      omega
  have indexUniv : (Finset.univ : Finset (DerivativeIndex 0)) =
      {zeroDerivativeIndex} := by
    ext index
    simp only [Finset.mem_univ, Finset.mem_singleton]
    exact ⟨fun _ => indexUnique index, fun _ => trivial⟩
  rw [indexUniv]
  simp only [Finset.sum_singleton]
  let zeroSplit : DerivativeSplit zeroDerivativeIndex :=
    (⟨0, by norm_num [zeroDerivativeIndex]⟩,
      ⟨0, by norm_num [zeroDerivativeIndex]⟩)
  have splitUnique (split : DerivativeSplit zeroDerivativeIndex) :
      split = zeroSplit := by
    apply Prod.ext
    · apply Fin.ext
      omega
    · apply Fin.ext
      omega
  have splitUniv : (Finset.univ : Finset (DerivativeSplit zeroDerivativeIndex)) =
      {zeroSplit} := by
    ext split
    simp only [Finset.mem_univ, Finset.mem_singleton]
    exact ⟨fun _ => splitUnique split, fun _ => trivial⟩
  rw [splitUniv]
  simp only [Finset.sum_singleton]
  norm_num [splitMultiplicity, zeroSplit, zeroDerivativeIndex]

theorem coefficientComposition_norm_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : Coefficient L sigma gamma ell grade middleDimension outputDimension)
    (inner : Coefficient L sigma gamma ell grade inputDimension middleDimension) :
    ‖coefficientComposition admissible grade outer inner‖ ≤
      gradeProductConstant grade * ‖outer‖ * ‖inner‖ := by
  exact rawComposition_norm_le admissible grade outer.1 inner.1

theorem coefficientComposition_base_norm_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    {inputDimension middleDimension outputDimension : ℕ}
    (outer : Coefficient L sigma gamma ell 0 middleDimension outputDimension)
    (inner : Coefficient L sigma gamma ell 0 inputDimension middleDimension) :
    ‖coefficientComposition admissible 0 outer inner‖ ≤ ‖outer‖ * ‖inner‖ := by
  simpa only [gradeProductConstant_zero, one_mul] using
    coefficientComposition_norm_le admissible 0 outer inner

end Grad.GaugeCoefficients.Algebra
