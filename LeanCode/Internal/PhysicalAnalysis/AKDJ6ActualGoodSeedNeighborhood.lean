import AKDJ5ActualProductInverse
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3500
open Set
open scoped Topology ContDiff
namespace Grad.OriginalInverseNeighborhood
open Grad.CartesianState Grad.Constraints Grad.Q24Realization Grad.RealFixedRanges
open Grad.NashMoser.OriginalIteration Grad.NashMoser.OriginalLimit

def originalSeedCenter : Seed.Parameters := ![0,Real.pi/4,1/4,1/4]

theorem originalSeedCenter_inside : originalSeedCenter ∈ Seed.parameterDomain := by
  change |(0:ℝ)| < 1
  norm_num

theorem originalSeedCenter_zero : originalSeedCenter 0 = 0 := rfl

theorem originalSeedAlpha_nonresonant (multiple : ℤ) :
    Real.pi/4 ≠ (Real.pi/2)*(multiple:ℝ) := by
  intro equal
  have cases : multiple ≤ 0 ∨ 1 ≤ multiple := by omega
  rcases cases with nonpositive | positive
  · have realNonpositive : (multiple:ℝ) ≤ 0 := by exact_mod_cast nonpositive
    have productNonpositive : (Real.pi/2)*(multiple:ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) realNonpositive
    linarith [Real.pi_pos]
  · have realPositive : (1:ℝ) ≤ (multiple:ℝ) := by exact_mod_cast positive
    have productLower : Real.pi/2 ≤ (Real.pi/2)*(multiple:ℝ) := by
      nlinarith [Real.pi_pos]
    linarith [Real.pi_pos]

/-- Openness of the constructed product gives a strictly positive good
seed. The central zero eccentricity is used only to construct the product. -/
theorem OriginalPhysicalProduct.exists_goodSeed {parameters : PhaseParameters} {positive : 0 < parameters.length}
    {reference : Seed.Parameters} {insideR : reference ∈ Seed.parameterDomain}
    (product : OriginalPhysicalProduct parameters positive reference insideR originalSeedCenter) :
    ∃ rho : ℝ, 0 < rho ∧ rho < 1/4 ∧
      ((![rho,Real.pi/4,1/4,1/4] : Seed.Parameters),0) ∈ interior product.neighborhood.parameterDomain := by
  let curve : ℝ → OriginalFiniteParameter := fun rho => (![rho,Real.pi/4,1/4,1/4],0)
  have continuous : Continuous curve := by
    apply Continuous.prodMk _ continuous_const
    apply continuous_pi
    intro coordinate
    fin_cases coordinate <;> fun_prop
  have openCurve : IsOpen (curve ⁻¹' product.neighborhood.parameterDomain) := product.openDomain.preimage continuous
  have zeroIn : (0:ℝ) ∈ curve ⁻¹' product.neighborhood.parameterDomain := product.centerMember
  obtain ⟨delta,deltaPositive,included⟩ := Metric.isOpen_iff.mp openCurve 0 zeroIn
  let rho := min (delta/2) (1/8)
  have rhoPositive : 0 < rho := lt_min (by positivity) (by norm_num)
  have rhoDelta : rho < delta := (min_le_left _ _).trans_lt (by linarith)
  have rhoSmall : rho < 1/4 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨rho,rhoPositive,rhoSmall,?_⟩
  rw [product.openDomain.interior_eq]
  apply included
  rw [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos rhoPositive]
  exact rhoDelta

/-- The actual product for the fixed nonresonant seed center. Its map and
both inverse laws are supplied by the preceding construction. -/
def canonicalOriginalPhysicalProduct (parameters : PhaseParameters) (positive : 0 < parameters.length) :
    OriginalPhysicalProduct parameters positive originalSeedCenter originalSeedCenter_inside originalSeedCenter :=
  actualOriginalPhysicalProduct parameters positive originalSeedCenter originalSeedCenter_inside
    originalSeedCenter originalSeedCenter_inside originalSeedCenter_zero

end Grad.OriginalInverseNeighborhood
