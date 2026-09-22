import SCD17DivisionRow

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial Grad.BoundaryTrace

def completedDivisionRow {dimension grade power radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (paid : power + radial + 3 ≤ grade) :
    AGrade parameters dimension grade →L[ℂ] DivisionRow dimension lower :=
  denseCoreExtension parameters (coreDivisionRowLinear lower positive bounded parameters paid)
    (Real.sqrt (finiteAngularBoundConstant power radial))
    (coreDivisionRow_norm_bound lower positive bounded parameters paid)

theorem completedDivisionRow_core {dimension grade power radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (paid : power + radial + 3 ≤ grade) (field : GradeCore parameters dimension grade) :
    completedDivisionRow lower positive bounded parameters paid (aGradeEta parameters field) =
      coreDivisionRowLinear lower positive bounded parameters paid field :=
  denseCoreExtension_apply_eta parameters _ _ _ field

theorem completedDivisionRow_bound {dimension grade power radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (paid : power + radial + 3 ≤ grade) (field : AGrade parameters dimension grade) :
    ‖completedDivisionRow lower positive bounded parameters paid field‖ ≤
      Real.sqrt (finiteAngularBoundConstant power radial) * ‖field‖ :=
  denseCoreExtension_apply_norm_le parameters _ _ _ field

/-- The literal sum of the radial L2 graph-coordinate norms. Each coordinate
itself is the full angular/cell Hilbert sum with exact nu^p. -/
abbrev DivisionJetArray (dimension : ℕ) (lower : ℝ) (radial : ℕ) :=
  PiLp 1 (fun _ : Fin (radial + 1) => DivisionRow dimension lower)

def completedDivisionArray {dimension : ℕ} (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ) :
    AGrade parameters dimension (power + radial + 3) →L[ℂ] DivisionJetArray dimension lower radial :=
  (PiLp.continuousLinearEquiv 1 ℂ (fun _ : Fin (radial + 1) => DivisionRow dimension lower)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun index : Fin (radial + 1) =>
      completedDivisionRow (power := power) (radial := index.val) lower positive bounded parameters (by omega)))

theorem completedDivisionArray_component {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ)
    (field : AGrade parameters dimension (power + radial + 3)) (index : Fin (radial + 1)) :
    completedDivisionArray lower positive bounded parameters power radial field index =
      completedDivisionRow (power := power) (radial := index.val) lower positive bounded parameters (by omega) field := rfl

theorem completedDivisionArray_norm {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ)
    (field : AGrade parameters dimension (power + radial + 3)) :
    ‖completedDivisionArray lower positive bounded parameters power radial field‖ =
      ∑ index : Fin (radial + 1),
        ‖completedDivisionRow (power := power) (radial := index.val) lower positive bounded parameters (by omega) field‖ := by
  rw [PiLp.norm_eq_of_L1]
  rfl

theorem completedDivisionArray_bound {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ)
    (field : AGrade parameters dimension (power + radial + 3)) :
    ‖completedDivisionArray lower positive bounded parameters power radial field‖ ≤
      divisionGraphConstant power radial * ‖field‖ := by
  rw [completedDivisionArray_norm]
  calc
    _ ≤ ∑ index : Fin (radial + 1), Real.sqrt (finiteAngularBoundConstant power index.val) * ‖field‖ :=
      Finset.sum_le_sum (fun index _ => completedDivisionRow_bound lower positive bounded parameters (by omega) field)
    _ = _ := by
      rw [← Finset.sum_mul]
      congr 1
      exact Fin.sum_univ_eq_sum_range (fun index => Real.sqrt (finiteAngularBoundConstant power index)) (radial + 1)

theorem completedDivisionArray_core_norm {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ) (field : ACore parameters dimension) :
    ‖completedDivisionArray lower positive bounded parameters power radial
      (aGradeEta parameters (GradeCore.ofCoreLinear field))‖ =
      originalDivisionGraphNorm lower power radial parameters field := by
  rw [completedDivisionArray_norm]
  simp_rw [completedDivisionRow_core]
  have normRoot : ∀ index : Fin (radial + 1),
      ‖coreDivisionRowLinear (power := power) (radial := index.val) lower positive bounded parameters
        (by omega : power + index.val + 3 ≤ power + radial + 3) (GradeCore.ofCoreLinear field)‖ =
      Real.sqrt (∑' mode : ℤ × ℤ, originalDivisionEnergy lower power index.val parameters field mode) := by
    intro index
    have energy := coreDivisionRow_norm_sq (power := power) (radial := index.val)
      lower positive bounded parameters (by omega : power + index.val + 3 ≤ power + radial + 3)
      (GradeCore.ofCoreLinear field)
    change _ = ∑' mode : ℤ × ℤ, originalDivisionEnergy lower power index.val parameters field mode at energy
    rw [← energy, Real.sqrt_sq (norm_nonneg _)]
  simp_rw [normRoot]
  exact Fin.sum_univ_eq_sum_range
    (fun index => Real.sqrt (∑' mode : ℤ × ℤ, originalDivisionEnergy lower power index parameters field mode))
    (radial + 1)

end Grad.SourceCollarDivision
