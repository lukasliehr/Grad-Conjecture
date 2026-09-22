import BL24FiniteCore

noncomputable section

open Set
open scoped BigOperators

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

def singletonBoundaryCore {dimension : ℕ} (parameters : PhaseParameters) (mode : ℤ × ℤ)
    (value : ComplexEuclidean dimension) : BoundaryCore parameters dimension := by
  classical
  refine ⟨fun output => if output = mode then value else 0, ?_⟩
  intro grade _
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
  apply summable_of_ne_finset_zero (s := {mode})
  intro output missing
  have different : output ≠ mode := by simpa only [Finset.mem_singleton] using missing
  simp only [if_neg different, smul_zero, norm_zero, ENNReal.toReal_ofNat, Real.rpow_two, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]

def singletonBoundaryCoreLinear (parameters : PhaseParameters) (dimension : ℕ) (mode : ℤ × ℤ) :
    ComplexEuclidean dimension →ₗ[ℂ] BoundaryCore parameters dimension where
  toFun := singletonBoundaryCore parameters mode
  map_add' first second := by
    apply Subtype.ext
    funext output
    by_cases equal : output = mode <;> simp [singletonBoundaryCore, equal]
  map_smul' scalar value := by
    apply Subtype.ext
    funext output
    by_cases equal : output = mode <;> simp [singletonBoundaryCore, equal]

def boundaryCoreEvaluation {dimension : ℕ} (parameters : PhaseParameters) (mode : ℤ × ℤ) :
    BoundaryCore parameters dimension →ₗ[ℂ] ComplexEuclidean dimension where
  toFun values := values.1 mode
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def angularBoundaryCoreLinear (parameters : PhaseParameters) (dimension : ℕ) (cell : ℤ) :
    (ℤ →₀ ComplexEuclidean dimension) →ₗ[ℂ] BoundaryCore parameters dimension :=
  Finsupp.lsum ℂ (fun mode => singletonBoundaryCoreLinear parameters dimension (mode, cell))

theorem angularBoundaryCoreLinear_coefficient {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (values : ℤ →₀ ComplexEuclidean dimension) (output : ℤ × ℤ) :
    (angularBoundaryCoreLinear parameters dimension cell values).1 output =
      if output.2 = cell then values output.1 else 0 := by
  classical
  change boundaryCoreEvaluation parameters output (angularBoundaryCoreLinear parameters dimension cell values) = _
  rw [angularBoundaryCoreLinear, Finsupp.lsum_apply, Finsupp.sum, map_sum]
  change (∑ mode ∈ values.support, if output = (mode, cell) then values mode else 0) = _
  by_cases cellEqual : output.2 = cell
  · have pairEquality (mode : ℤ) : output = (mode, cell) ↔ output.1 = mode := by
      exact ⟨fun equality => congrArg Prod.fst equality, fun equality => Prod.ext equality cellEqual⟩
    simp_rw [pairEquality]
    rw [if_pos cellEqual, Finset.sum_ite_eq]
    by_cases member : output.1 ∈ values.support
    · rw [if_pos member]
    · have zeroValue : values output.1 = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using member
      rw [if_neg member, zeroValue]
  · have pairNe (mode : ℤ) : output ≠ (mode, cell) := fun equality => cellEqual (congrArg Prod.snd equality)
    simp only [if_neg cellEqual, if_neg (pairNe _), Finset.sum_const_zero]

def finiteBoundaryCoreLinear (parameters : PhaseParameters) (dimension : ℕ) :
    FiniteBoundaryData dimension →ₗ[ℂ] BoundaryCore parameters dimension :=
  Finsupp.lsum ℂ (fun cell => angularBoundaryCoreLinear parameters dimension cell)

theorem finiteBoundaryCoreLinear_coefficient {dimension : ℕ} (parameters : PhaseParameters)
    (values : FiniteBoundaryData dimension) (output : ℤ × ℤ) :
    (finiteBoundaryCoreLinear parameters dimension values).1 output = values output.2 output.1 := by
  classical
  change boundaryCoreEvaluation parameters output (finiteBoundaryCoreLinear parameters dimension values) = _
  rw [finiteBoundaryCoreLinear, Finsupp.lsum_apply, Finsupp.sum, map_sum]
  change (∑ cell ∈ values.support, (angularBoundaryCoreLinear parameters dimension cell (values cell)).1 output) = _
  simp_rw [angularBoundaryCoreLinear_coefficient]
  rw [Finset.sum_ite_eq]
  by_cases member : output.2 ∈ values.support
  · rw [if_pos member]
  · have zeroValue : values output.2 = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using member
    rw [if_neg member, zeroValue, Finsupp.zero_apply]

def finiteBoundaryToGrade {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) :
    FiniteBoundaryData dimension →ₗ[ℂ] BoundaryGrade parameters (ComplexEuclidean dimension) grade :=
  (boundaryToGrade parameters grade gradePositive).comp (finiteBoundaryCoreLinear parameters dimension)

theorem finiteBoundaryToGrade_coefficient {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (values : FiniteBoundaryData dimension) (output : ℤ × ℤ) :
    boundaryCoefficient parameters grade (finiteBoundaryToGrade parameters grade gradePositive values) output =
      values output.2 output.1 := by
  rw [finiteBoundaryToGrade, LinearMap.comp_apply, boundaryToGrade_coefficient,
    finiteBoundaryCoreLinear_coefficient]

end Grad.BoundaryLift
