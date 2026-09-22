import AKC1SameConjugatedKernelAction
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open Set Filter
open scoped Topology
namespace Grad.AnnularWeightedSmoothness

section Resolvent
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

omit [NormedAlgebra ℝ R] in
theorem reservedResolvent_identity (first second inverseFirst inverseSecond reserve higherInverse : R)
    (right : first * inverseFirst = 1) (left : inverseSecond * second = 1)
    (coherent : inverseFirst * reserve = reserve * higherInverse) :
    (inverseSecond - inverseFirst) * reserve =
      -(inverseSecond * ((second - first) * reserve)) * higherInverse := by
  have firstTerm : inverseSecond * (second * (inverseFirst * reserve)) = inverseFirst * reserve := by
    rw [← mul_assoc inverseSecond second, left, one_mul]
  have secondTerm : inverseSecond * (first * (inverseFirst * reserve)) = inverseSecond * reserve := by
    rw [← mul_assoc first inverseFirst, right, one_mul]
  calc
    _ = inverseSecond * reserve - inverseFirst * reserve := sub_mul _ _ _
    _ = -(inverseSecond * ((second - first) * (inverseFirst * reserve))) := by
      rw [sub_mul, mul_sub, firstTerm, secondTerm, neg_sub]
    _ = _ := by rw [coherent]; simp only [mul_assoc, neg_mul]

theorem reservedResolvent_slope (forward inverse : ℝ → R) (reserve higherInverse : R)
    (base point : ℝ) (right : forward base * inverse base = 1)
    (left : inverse point * forward point = 1)
    (coherent : inverse base * reserve = reserve * higherInverse) :
    slope (fun radius => inverse radius * reserve) base point =
      -(inverse point * slope (fun radius => forward radius * reserve) base point) * higherInverse := by
  simp only [slope, vsub_eq_sub]
  rw [← sub_mul, reservedResolvent_identity _ _ _ _ _ _ right left coherent]
  simp only [mul_smul_comm, sub_mul]
  rw [← smul_mul_assoc, smul_neg]

/-- A genuine derivative of the SAME inverse with a reserve follows from
only norm continuity of the inverse and the reserved forward derivative. -/
theorem reservedInverse_hasDerivWithinAt (domain : Set ℝ) (forward inverse : ℝ → R)
    (reserve higherInverse derivative : R) (base : ℝ)
    (right : forward base * inverse base = 1)
    (left : ∀ point ∈ domain, inverse point * forward point = 1)
    (coherent : inverse base * reserve = reserve * higherInverse)
    (continuous : ContinuousWithinAt inverse domain base)
    (differentiable : HasDerivWithinAt (fun point => forward point * reserve) derivative domain base) :
    HasDerivWithinAt (fun point => inverse point * reserve)
      (-(inverse base * derivative) * higherInverse) domain base := by
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  have inverseLimit : Tendsto inverse (𝓝[domain \ {base}] base) (𝓝 (inverse base)) :=
    (continuous.mono sdiff_subset).tendsto
  have slopeLimit := hasDerivWithinAt_iff_tendsto_slope.mp differentiable
  have product := ((inverseLimit.mul slopeLimit).neg).mul (tendsto_const_nhds (x := higherInverse))
  apply product.congr'
  filter_upwards [self_mem_nhdsWithin] with point inside
  exact (reservedResolvent_slope forward inverse reserve higherInverse base point right (left point inside.1) coherent).symm

/-- The scale resolvent only needs continuity after a fixed left reserve. -/
theorem leftReservedResolvent_slope (forward inverse : ℝ → R)
    (leftReserve reserve higherInverse : R) (base point : ℝ)
    (right : forward base * inverse base = 1)
    (left : inverse point * forward point = 1)
    (coherent : inverse base * reserve = reserve * higherInverse) :
    slope (fun radius => leftReserve * inverse radius * reserve) base point =
      -((leftReserve * inverse point) * slope (fun radius => forward radius * reserve) base point) * higherInverse := by
  have same : slope (fun radius => leftReserve * inverse radius * reserve) base point =
      leftReserve * slope (fun radius => inverse radius * reserve) base point := by
    simp only [slope, vsub_eq_sub, mul_smul_comm, mul_sub, mul_assoc]
  rw [same, reservedResolvent_slope forward inverse reserve higherInverse base point right left coherent]
  simp only [mul_assoc, mul_neg, neg_mul]

theorem leftReservedInverse_hasDerivWithinAt (domain : Set ℝ) (forward inverse : ℝ → R)
    (leftReserve reserve higherInverse derivative : R) (base : ℝ)
    (right : forward base * inverse base = 1)
    (left : ∀ point ∈ domain, inverse point * forward point = 1)
    (coherent : inverse base * reserve = reserve * higherInverse)
    (continuous : ContinuousWithinAt (fun point => leftReserve * inverse point) domain base)
    (differentiable : HasDerivWithinAt (fun point => forward point * reserve) derivative domain base) :
    HasDerivWithinAt (fun point => leftReserve * inverse point * reserve)
      (-((leftReserve * inverse base) * derivative) * higherInverse) domain base := by
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  have inverseLimit : Tendsto (fun point => leftReserve * inverse point) (𝓝[domain \ {base}] base) (𝓝 (leftReserve * inverse base)) :=
    (continuous.mono sdiff_subset).tendsto
  have slopeLimit := hasDerivWithinAt_iff_tendsto_slope.mp differentiable
  have product := ((inverseLimit.mul slopeLimit).neg).mul (tendsto_const_nhds (x := higherInverse))
  apply product.congr'
  filter_upwards [self_mem_nhdsWithin] with point inside
  exact (leftReservedResolvent_slope forward inverse leftReserve reserve higherInverse base point right (left point inside.1) coherent).symm

end Resolvent
end Grad.AnnularWeightedSmoothness
