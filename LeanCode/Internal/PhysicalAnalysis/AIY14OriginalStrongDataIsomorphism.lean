import AIY13ReconstructOriginalStrongData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option synthInstance.maxHeartbeats 400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularStrongData
open Grad.CartesianState Grad.AnnularCurrentSource Grad.AnnularLowEnergy Grad.AnnularCrossMaps

private theorem injectiveOfNormLowerBound {E F : Type*}
    [NormedAddCommGroup E] [Module ℝ E] [NormedAddCommGroup F] [Module ℝ F]
    (mapping : E →L[ℝ] F) (C : ℝ) (bound : ∀ x, ‖x‖ ≤ C * ‖mapping x‖) :
    Function.Injective mapping := by
  intro first second same
  have difference := bound (first - second)
  rw [map_sub, same, sub_self, norm_zero, mul_zero] at difference
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm difference (norm_nonneg _)))

private theorem linearEquivInverseBound {E F : Type*}
    [NormedAddCommGroup E] [Module ℝ E] [NormedAddCommGroup F] [Module ℝ F]
    (equivalence : E ≃ₗ[ℝ] F) (C : ℝ) (bound : ∀ x, ‖x‖ ≤ C * ‖equivalence x‖) (y : F) :
    ‖equivalence.symm y‖ ≤ C * ‖y‖ := by
  have result := bound (equivalence.symm y)
  rw [equivalence.apply_symm_apply] at result
  exact result

private def continuousEquivOfBounds {E F : Type*}
    [NormedAddCommGroup E] [Module ℝ E] [NormedAddCommGroup F] [Module ℝ F]
    (equivalence : E ≃ₗ[ℝ] F) (C D : ℝ)
    (forward : ∀ x, ‖equivalence x‖ ≤ C * ‖x‖)
    (backward : ∀ y, ‖equivalence.symm y‖ ≤ D * ‖y‖) : E ≃L[ℝ] F where
  toLinearEquiv := equivalence
  continuous_toFun := (equivalence.toLinearMap.mkContinuous C forward).continuous
  continuous_invFun := (equivalence.symm.toLinearMap.mkContinuous D backward).continuous

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length) (angular cell : ℕ)

theorem strongToOriginal_injective :
    Function.Injective (strongToOriginal parameters lower angular cell length positive bounded lengthPositive) :=
  injectiveOfNormLowerBound
    (strongToOriginal parameters lower angular cell length positive bounded lengthPositive)
    ((10 + originalLowIncomingConstant parameters length) * lower ^ (-9 / 4 : ℝ))
    (strongOriginalCoordinateMap_lowerBound parameters lower length positive bounded lengthPositive angular cell)

theorem strongToOriginal_bijective :
    Function.Bijective (strongToOriginal parameters lower angular cell length positive bounded lengthPositive) :=
  ⟨strongToOriginal_injective parameters lower length positive bounded lengthPositive angular cell,
    fun data => ⟨originalToStrong parameters lower length positive bounded lengthPositive angular cell data,
      strongToOriginal_originalToStrong parameters lower length positive bounded lengthPositive angular cell data⟩⟩

def strongOriginalLinearEquiv :
    StrongDataCarrier parameters lower positive bounded angular cell ≃ₗ[ℝ]
      OriginalStrongCarrier parameters lower angular cell :=
  LinearEquiv.ofBijective (strongToOriginal parameters lower angular cell length positive bounded lengthPositive).toLinearMap
    (strongToOriginal_bijective parameters lower length positive bounded lengthPositive angular cell)

theorem strongOriginalLinearEquiv_inverse_bound
    (data : OriginalStrongCarrier parameters lower angular cell) :
    ‖(strongOriginalLinearEquiv parameters lower length positive bounded lengthPositive angular cell).symm data‖ ≤
      ((10 + originalLowIncomingConstant parameters length) * lower ^ (-9 / 4 : ℝ)) * ‖data‖ :=
  linearEquivInverseBound
    (strongOriginalLinearEquiv parameters lower length positive bounded lengthPositive angular cell)
    ((10 + originalLowIncomingConstant parameters length) * lower ^ (-9 / 4 : ℝ))
    (strongOriginalCoordinateMap_lowerBound parameters lower length positive bounded lengthPositive angular cell) data

def originalStrongWeightMap : OriginalStrongCarrier parameters lower angular cell →L[ℝ]
    StrongDataCarrier parameters lower positive bounded angular cell :=
  (strongOriginalLinearEquiv parameters lower length positive bounded lengthPositive angular cell).symm.toLinearMap.mkContinuous
    ((10 + originalLowIncomingConstant parameters length) * lower ^ (-9 / 4 : ℝ))
    (strongOriginalLinearEquiv_inverse_bound parameters lower length positive bounded lengthPositive angular cell)

/-- BF5 as an actual bounded linear isomorphism on the independently defined
original and weighted complete Hilbert carriers, with both inverse laws. -/
def originalStrongWeightEquivalence : OriginalStrongCarrier parameters lower angular cell ≃L[ℝ]
    StrongDataCarrier parameters lower positive bounded angular cell :=
  continuousEquivOfBounds
    (strongOriginalLinearEquiv parameters lower length positive bounded lengthPositive angular cell).symm
    ((10 + originalLowIncomingConstant parameters length) * lower ^ (-9 / 4 : ℝ))
    (7 + 2 * lowOuterFrequencyConstant length)
    (strongOriginalLinearEquiv_inverse_bound parameters lower length positive bounded lengthPositive angular cell)
    (strongOriginalCoordinateMap_bound parameters lower positive bounded angular cell length lengthPositive)

theorem originalStrongWeightEquivalence_bound
    (data : OriginalStrongCarrier parameters lower angular cell) :
    ‖originalStrongWeightEquivalence parameters lower length positive bounded lengthPositive angular cell data‖ ≤
      ((10 + originalLowIncomingConstant parameters length) * lower ^ (-9 / 4 : ℝ)) * ‖data‖ :=
  strongOriginalLinearEquiv_inverse_bound parameters lower length positive bounded lengthPositive angular cell data

theorem originalStrongWeightEquivalence_inverse_bound
    (data : StrongDataCarrier parameters lower positive bounded angular cell) :
    ‖(originalStrongWeightEquivalence parameters lower length positive bounded lengthPositive angular cell).symm data‖ ≤
      (7 + 2 * lowOuterFrequencyConstant length) * ‖data‖ :=
  strongOriginalCoordinateMap_bound parameters lower positive bounded angular cell length lengthPositive data

/-- The abstract Hilbert isomorphism is exactly the explicit reconstruction
from the original source graphs and original six physical forcing rows. -/
theorem originalStrongWeightEquivalence_eq_reconstruction
    (data : OriginalStrongCarrier parameters lower angular cell) :
    originalStrongWeightEquivalence parameters lower length positive bounded lengthPositive angular cell data =
      originalToStrong parameters lower length positive bounded lengthPositive angular cell data := by
  apply strongToOriginal_injective parameters lower length positive bounded lengthPositive angular cell
  exact (strongOriginalLinearEquiv parameters lower length positive bounded lengthPositive angular cell).apply_symm_apply data |>.trans
    (strongToOriginal_originalToStrong parameters lower length positive bounded lengthPositive angular cell data).symm

end Grad.AnnularStrongData
