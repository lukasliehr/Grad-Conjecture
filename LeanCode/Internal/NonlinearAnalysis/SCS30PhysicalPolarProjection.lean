import SCS29OriginalPhysicalSource

noncomputable section

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.BoundaryTrace Grad.Constraints.Gauges

def radialProjection (angle : ℝ) : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 1 :=
  (Real.cos angle : ℂ) • planarComponentMap 0 + (Real.sin angle : ℂ) • planarComponentMap 1

def tangentialProjection (angle : ℝ) : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 1 :=
  (Real.cos angle : ℂ) • planarComponentMap 1 - (Real.sin angle : ℂ) • planarComponentMap 0

theorem radialProjection_continuous : Continuous radialProjection :=
  ((Complex.continuous_ofReal.comp Real.continuous_cos).smul continuous_const).add
    ((Complex.continuous_ofReal.comp Real.continuous_sin).smul continuous_const)

theorem tangentialProjection_continuous : Continuous tangentialProjection :=
  ((Complex.continuous_ofReal.comp Real.continuous_cos).smul continuous_const).sub
    ((Complex.continuous_ofReal.comp Real.continuous_sin).smul continuous_const)

theorem radialProjection_apply (angle : ℝ) (field : ℝ → ComplexEuclidean 2) :
    radialProjection angle (field angle) = radialPolarField field angle := by
  simp only [radialProjection, add_apply, smul_apply,
    radialPolarField, map_smul]

theorem tangentialProjection_apply (angle : ℝ) (field : ℝ → ComplexEuclidean 2) :
    tangentialProjection angle (field angle) = tangentialPolarField field angle := by
  simp only [tangentialProjection, sub_apply, smul_apply,
    tangentialPolarField, map_smul]

theorem angularCoefficient_real_smul {dimension : ℕ} (scalar : ℝ)
    (field : ℝ → ComplexEuclidean dimension) (mode : ℤ) :
    angularCoefficient (fun angle => scalar • field angle) mode = scalar • angularCoefficient field mode := by
  have expression : (fun angle => scalar • field angle) = (scalar : ℂ) • field := by
    funext angle
    exact (Complex.coe_smul scalar (field angle)).symm
  rw [expression, angularCoefficient_smul_continuous, Complex.coe_smul]

end Grad.SourceCollarFullSource
