import AKDQ21ActualForcePairingsZero
import LiteralRowAlgebra

noncomputable section
open Set

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily Grad.NonlinearQuotient
open Grad.MainAssembly.SampledAxisBasics Grad.MainAssembly.PhysicalNormalHessian
open Grad.PhysicalFamily.SampledFullGeometry Grad.PhysicalFamily.SampledGlobalEmbedding

theorem plane_linear_zero_of_radial_angular (linear : Plane →L[ℝ] ℝ) (point : Plane) (nonzero : point ≠ 0)
    (radial : linear point = 0) (angular : linear (planeQuarterTurn point) = 0) :
    ∀ direction : Plane, linear direction = 0 := by
  rw [disk_basis_decomposition point, map_add, map_smul, map_smul] at radial
  rw [disk_quarterTurn_decomposition point, map_add, map_smul, map_smul] at angular
  simp only [smul_eq_mul] at radial angular
  have positive : 0 < point 0 ^ 2 + point 1 ^ 2 := by
    rw [← disk_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr nonzero)
  have first : (point 0 ^ 2 + point 1 ^ 2) * linear (diskBasis 0) = 0 := by
    linear_combination point 0 * radial - point 1 * angular
  have second : (point 0 ^ 2 + point 1 ^ 2) * linear (diskBasis 1) = 0 := by
    linear_combination point 1 * radial + point 0 * angular
  have firstZero := (mul_eq_zero.mp first).resolve_left positive.ne'
  have secondZero := (mul_eq_zero.mp second).resolve_left positive.ne'
  intro direction
  rw [disk_basis_decomposition direction, map_add, map_smul, map_smul, firstZero, secondZero]
  simp

/-- Away from the axis the actual radial, angular and axial directions
span the full physical tangent space through an injective position derivative. -/
theorem vector_zero_of_coordinate_pairings (linear : Vec →L[ℝ] Vec)
    (injective : Function.Injective linear) (point : Plane) (nonzero : point ≠ 0) (value : Vec)
    (radial : inner ℝ value (linear (coordinateDirection point 0)) = 0)
    (angular : inner ℝ value (linear (coordinateDirection (planeQuarterTurn point) 0)) = 0)
    (temporal : inner ℝ value (linear (coordinateDirection 0 1)) = 0) : value = 0 := by
  let functional : Vec →L[ℝ] ℝ := (innerSL ℝ value).comp linear
  let planar : Plane →L[ℝ] ℝ := functional.comp physicalDiskCLM
  have planarZero : ∀ direction, planar direction = 0 :=
    plane_linear_zero_of_radial_angular planar point nonzero radial angular
  have wholeZero (direction : Vec) : functional direction = 0 := by
    have decomposition : direction = coordinateDirection (planarPart direction) (direction 2) := by
      ext coordinate
      fin_cases coordinate <;> simp [coordinateDirection, planarPart, vector]
    rw [decomposition, coordinateDirection_add, map_add]
    have firstZero : functional (coordinateDirection (planarPart direction) 0) = 0 := planarZero _
    have timeScale : coordinateDirection 0 (direction 2) = (direction 2) • coordinateDirection 0 1 := by
      ext coordinate
      fin_cases coordinate <;> simp [coordinateDirection, vector]
    rw [firstZero, timeScale, map_smul]
    change 0 + direction 2 • inner ℝ value (linear (coordinateDirection 0 1)) = 0
    rw [temporal, smul_zero, add_zero]
  obtain ⟨preimage, same⟩ := LinearMap.injective_iff_surjective.mp injective value
  change linear preimage = value at same
  have zero := wholeZero preimage
  change inner ℝ value (linear preimage) = 0 at zero
  rw [same, inner_self_eq_zero] at zero
  exact zero

end Grad.PhysicalEquilibrium
