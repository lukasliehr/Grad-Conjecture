import RSC6RestrictionRow

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.SourceCollarRestriction

open Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial Grad.BoundaryTrace

def completedRestrictionRow {dimension grade power radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (paid : power + radial ≤ grade) :
    AGrade parameters dimension grade →L[ℂ] DivisionRow dimension lower :=
  denseCoreExtension parameters (coreRestrictionRowLinear lower positive bounded parameters paid)
    (Real.sqrt (restrictionRowConstant power radial))
    (coreRestrictionRow_norm_bound lower positive bounded parameters paid)

theorem completedRestrictionRow_core {dimension grade power radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (paid : power + radial ≤ grade) (field : GradeCore parameters dimension grade) :
    completedRestrictionRow lower positive bounded parameters paid (aGradeEta parameters field) =
      coreRestrictionRowLinear lower positive bounded parameters paid field :=
  denseCoreExtension_apply_eta parameters _ _ _ field

theorem completedRestrictionRow_bound {dimension grade power radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (paid : power + radial ≤ grade) (field : AGrade parameters dimension grade) :
    ‖completedRestrictionRow lower positive bounded parameters paid field‖ ≤
      Real.sqrt (restrictionRowConstant power radial) * ‖field‖ :=
  denseCoreExtension_apply_norm_le parameters _ _ _ field

def completedRestrictionArray {dimension : ℕ} (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ) :
    AGrade parameters dimension (power + radial) →L[ℂ] DivisionJetArray dimension lower radial :=
  (PiLp.continuousLinearEquiv 1 ℂ (fun _ : Fin (radial + 1) => DivisionRow dimension lower)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun index : Fin (radial + 1) =>
      completedRestrictionRow (power := power) (radial := index.val) lower positive bounded parameters (by omega)))

theorem completedRestrictionArray_component {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ)
    (field : AGrade parameters dimension (power + radial)) (index : Fin (radial + 1)) :
    completedRestrictionArray lower positive bounded parameters power radial field index =
      completedRestrictionRow (power := power) (radial := index.val) lower positive bounded parameters (by omega) field := rfl

theorem completedRestrictionArray_norm {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ)
    (field : AGrade parameters dimension (power + radial)) :
    ‖completedRestrictionArray lower positive bounded parameters power radial field‖ =
      ∑ index : Fin (radial + 1),
        ‖completedRestrictionRow (power := power) (radial := index.val) lower positive bounded parameters (by omega) field‖ := by
  rw [PiLp.norm_eq_of_L1]
  rfl

theorem completedRestrictionArray_bound {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ)
    (field : AGrade parameters dimension (power + radial)) :
    ‖completedRestrictionArray lower positive bounded parameters power radial field‖ ≤
      restrictionGraphConstant power radial * ‖field‖ := by
  rw [completedRestrictionArray_norm]
  calc
    _ ≤ ∑ index : Fin (radial + 1), Real.sqrt (restrictionRowConstant power index.val) * ‖field‖ :=
      Finset.sum_le_sum (fun index _ => completedRestrictionRow_bound lower positive bounded parameters (by omega) field)
    _ = _ := by
      rw [← Finset.sum_mul]
      congr 1
      exact Fin.sum_univ_eq_sum_range (fun index => Real.sqrt (restrictionRowConstant power index)) (radial + 1)

theorem completedRestrictionArray_core_norm {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ) (field : ACore parameters dimension) :
    ‖completedRestrictionArray lower positive bounded parameters power radial
      (aGradeEta parameters (GradeCore.ofCoreLinear field))‖ =
      originalRestrictionGraphNorm lower power radial parameters field := by
  rw [completedRestrictionArray_norm]
  simp_rw [completedRestrictionRow_core]
  have normRoot : ∀ index : Fin (radial + 1),
      ‖coreRestrictionRowLinear (power := power) (radial := index.val) lower positive bounded parameters
        (by omega : power + index.val ≤ power + radial) (GradeCore.ofCoreLinear field)‖ =
      Real.sqrt (∑' mode : ℤ × ℤ, originalRestrictionEnergy lower power index.val parameters field mode) := by
    intro index
    have energy := coreRestrictionRow_norm_sq (power := power) (radial := index.val)
      lower positive bounded parameters (by omega : power + index.val ≤ power + radial)
      (GradeCore.ofCoreLinear field)
    change _ = ∑' mode : ℤ × ℤ, originalRestrictionEnergy lower power index.val parameters field mode at energy
    rw [← energy, Real.sqrt_sq (norm_nonneg _)]
  simp_rw [normRoot]
  exact Fin.sum_univ_eq_sum_range
    (fun index => Real.sqrt (∑' mode : ℤ × ℤ, originalRestrictionEnergy lower power index parameters field mode))
    (radial + 1)

end Grad.SourceCollarRestriction
