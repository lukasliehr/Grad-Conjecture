import GC12Interface

noncomputable section

set_option maxHeartbeats 3000000

open Grad.GenericCarriers Grad.ClosedJets Grad.GaugeCoefficients.Envelope
open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Neumann.Regularity

open Grad.GaugeCoefficients.Algebra

@[simp] theorem derivativeOrder_zeroDerivativeIndexAt (grade : ℕ) :
    derivativeOrder (zeroDerivativeIndexAt grade) = 0 := by
  simp [derivativeOrder, zeroDerivativeIndexAt]

def zeroDerivativeSplitAt (grade : ℕ) :
    DerivativeSplit (zeroDerivativeIndexAt grade) :=
  (⟨0, by simp [zeroDerivativeIndexAt]⟩,
    ⟨0, by simp [zeroDerivativeIndexAt]⟩)

theorem derivativeSplit_zeroAt_eq (grade : ℕ)
    (split : DerivativeSplit (zeroDerivativeIndexAt grade)) :
    split = zeroDerivativeSplitAt grade := by
  apply Prod.ext <;> apply Fin.ext <;> simp [zeroDerivativeIndexAt]

theorem derivativeSplit_zeroAt_univ (grade : ℕ) :
    (Finset.univ : Finset (DerivativeSplit (zeroDerivativeIndexAt grade))) =
      {zeroDerivativeSplitAt grade} := by
  ext split
  simp only [Finset.mem_univ, Finset.mem_singleton]
  exact ⟨fun _ => derivativeSplit_zeroAt_eq grade split, fun _ => trivial⟩

@[simp] theorem lowerDerivativeIndex_zeroAt (grade : ℕ) :
    lowerDerivativeIndex (zeroDerivativeIndexAt grade)
      (zeroDerivativeSplitAt grade) = zeroDerivativeIndexAt grade := by
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> rfl

@[simp] theorem upperDerivativeIndex_zeroAt (grade : ℕ) :
    upperDerivativeIndex (zeroDerivativeIndexAt grade)
      (zeroDerivativeSplitAt grade) = zeroDerivativeIndexAt grade := by
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> rfl

@[simp] theorem splitMultiplicity_zeroAt (grade : ℕ) :
    splitMultiplicity (zeroDerivativeIndexAt grade)
      (zeroDerivativeSplitAt grade) = 1 := by
  norm_num [splitMultiplicity, zeroDerivativeSplitAt, zeroDerivativeIndexAt]

theorem coefficientScale_cell_zero_zeroAt
    (L sigma gamma ell : ℝ) (grade : ℕ) (point : ClosedDisk) :
    coefficientScale L sigma gamma ell grade 0 (zeroDerivativeIndexAt grade) point = 1 := by
  simp [coefficientScale, originalEnvelope, scaledCellWeight,
    derivativeOrder_zeroDerivativeIndexAt]

/-- The constant identity belongs to every original coefficient grade. -/
def gradedIdentityCoefficient (L sigma gamma ell : ℝ) (grade dimension : ℕ) :
    Coefficient L sigma gamma ell grade dimension dimension :=
  coreInclusion L sigma gamma ell grade dimension dimension
    ⟨weightedSingle L sigma gamma ell grade 0 (identitySmoothOperatorJet dimension),
      Submodule.subset_span (Set.mem_range.mpr
        ⟨(0, identitySmoothOperatorJet dimension), rfl⟩)⟩

theorem gradedIdentityCoefficient_zeroDerivative
    (L sigma gamma ell : ℝ) (grade dimension : ℕ)
    (cell : ℤ) (point : ClosedDisk) :
    coefficientDerivative
        (gradedIdentityCoefficient L sigma gamma ell grade dimension)
        cell (zeroDerivativeIndexAt grade) point =
      if cell = 0 then ContinuousLinearMap.id ℂ (PhysicalValue dimension) else 0 := by
  change ((coefficientScale L sigma gamma ell grade cell
      (zeroDerivativeIndexAt grade) point : ℂ)⁻¹) •
      weightedSingle L sigma gamma ell grade 0
        (identitySmoothOperatorJet dimension) (cell, zeroDerivativeIndexAt grade) point = _
  rw [weightedSingle_apply]
  by_cases same : cell = 0
  · subst cell
    rw [if_pos rfl, if_pos rfl]
    change ((coefficientScale L sigma gamma ell grade 0
        (zeroDerivativeIndexAt grade) point : ℂ)⁻¹) •
      ((coefficientScale L sigma gamma ell grade 0
          (zeroDerivativeIndexAt grade) point : ℂ) •
        smoothOperatorDerivative (identitySmoothOperatorJet dimension) (0, 0) point) = _
    rw [identitySmoothOperatorJet_zero_derivative,
      coefficientScale_cell_zero_zeroAt]
    simp [identitySmoothValue]
  · rw [if_neg same, if_neg same]
    apply ContinuousLinearMap.ext
    intro value
    simp

theorem gradedIdentity_realizes
    (L sigma gamma ell : ℝ) (grade dimension : ℕ) :
    RealizesSameCoefficient (identityCoefficient L sigma gamma ell dimension)
      (gradedIdentityCoefficient L sigma gamma ell grade dimension) := by
  intro cell point
  rw [gradedIdentityCoefficient_zeroDerivative, identityCoefficient_value]

theorem realizesSameCoefficient_composition {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    {outerBase innerBase : BaseCoefficient L sigma gamma ell dimension}
    {outer inner : Coefficient L sigma gamma ell grade dimension dimension}
    (outerRealizes : RealizesSameCoefficient outerBase outer)
    (innerRealizes : RealizesSameCoefficient innerBase inner) :
    RealizesSameCoefficient
      (coefficientComposition admissible 0 outerBase innerBase)
      (coefficientComposition admissible grade outer inner) := by
  intro cell point
  rw [coefficientComposition_derivative]
  unfold formalCompositionDerivative
  rw [coefficientComposition_value]
  apply tsum_congr
  intro first
  rw [derivativeSplit_zeroAt_univ]
  simp only [Finset.sum_singleton, splitMultiplicity_zeroAt, Nat.cast_one,
    one_smul, lowerDerivativeIndex_zeroAt, upperDerivativeIndex_zeroAt]
  rw [outerRealizes, innerRealizes]

end Grad.GaugeCoefficients.Neumann.Regularity
