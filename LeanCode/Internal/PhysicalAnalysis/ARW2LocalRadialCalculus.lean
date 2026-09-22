import ARW1ActualPolarField

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators
namespace Grad.ActualRadialWords
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighRegularity
open Grad.CollarCartesian Grad.BoundaryLift Grad.BoundaryTrace Grad.FourierGrade

theorem radialWithin_hasDerivAt (profile : ℝ → ComplexEuclidean 1)
    (smooth : ContDiffOn ℝ ∞ profile (Icc (1 / 2 : ℝ) 1))
    (order : ℕ) (radius : ℝ) (inside : radius ∈ Ioo (1 / 2 : ℝ) 1) :
    HasDerivAt (iteratedDerivWithin order profile (Icc (1 / 2 : ℝ) 1))
      (iteratedDerivWithin (order + 1) profile (Icc (1 / 2 : ℝ) 1) radius) radius := by
  have member : radius ∈ Icc (1 / 2 : ℝ) 1 := ⟨inside.1.le, inside.2.le⟩
  have differentiable := smooth.differentiableOn_iteratedDerivWithin
    (m := order) (by exact_mod_cast (WithTop.coe_lt_top order : (order : ℕ∞) < ⊤))
    (uniqueDiffOn_Icc (by norm_num : (1 / 2 : ℝ) < 1)) radius member
  rw [iteratedDerivWithin_succ]
  exact differentiable.hasDerivWithinAt.hasDerivAt (Icc_mem_nhds inside.1 inside.2)

def polarRadialDerivative (mode : ℤ) (profile : ℝ → ComplexEuclidean 1) (order : ℕ)
    (point : ℝ × ℝ) : ComplexEuclidean 1 :=
  cellExponential mode point.2 • iteratedDerivWithin order profile (Icc (1 / 2 : ℝ) 1) (1 - point.1)

theorem polarRadialDerivative_hasFDerivAt (mode : ℤ) (profile : ℝ → ComplexEuclidean 1)
    (smooth : ContDiffOn ℝ ∞ profile (Icc (1 / 2 : ℝ) 1))
    (order : ℕ) (point : ℝ × ℝ) (inside : point ∈ openHalfCollar) :
    HasFDerivAt (polarRadialDerivative mode profile order)
      (cellExponential mode point.2 •
        ((ContinuousLinearMap.toSpanSingleton ℝ
          (iteratedDerivWithin (order + 1) profile (Icc (1 / 2 : ℝ) 1) (1 - point.1))).comp
          (-(ContinuousLinearMap.fst ℝ ℝ ℝ))) +
       ((cellExponentialDerivative mode point.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)).smulRight
         (iteratedDerivWithin order profile (Icc (1 / 2 : ℝ) 1) (1 - point.1))) point := by
  have reflected : 1 - point.1 ∈ Ioo (1 / 2 : ℝ) 1 := by
    constructor <;> linarith [inside.1.1, inside.1.2]
  have first := (radialWithin_hasDerivAt profile smooth order (1 - point.1) reflected).hasFDerivAt.comp point
    ((hasFDerivAt_const (c := (1 : ℝ)) point).sub (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt)
  have second := (cellExponential_hasFDerivAt mode point.2).comp point
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
  convert second.smul first using 1 <;> first | rfl | (simp only [zero_sub]; rfl)

theorem polarRadialDerivative_coordinate (mode : ℤ) (profile : ℝ → ComplexEuclidean 1)
    (smooth : ContDiffOn ℝ ∞ profile (Icc (1 / 2 : ℝ) 1))
    (order : ℕ) (point : ℝ × ℝ) (inside : point ∈ openHalfCollar) (coordinate : Fin 2) :
    fderiv ℝ (polarRadialDerivative mode profile order) point (productBasis coordinate) =
      if coordinate = 0 then -polarRadialDerivative mode profile (order + 1) point
      else (Complex.I * (mode : ℂ)) • polarRadialDerivative mode profile order point := by
  rw [(polarRadialDerivative_hasFDerivAt mode profile smooth order point inside).fderiv]
  have basis : ∀ c : Fin 2, productBasis c = if c = 0 then ((1, 0) : ℝ × ℝ) else (0, 1) := by
    intro c
    fin_cases c <;> rfl
  rw [basis]
  fin_cases coordinate <;>
    simp [cellExponentialDerivative, polarRadialDerivative, ContinuousLinearMap.toSpanSingleton_apply, mul_smul]

end Grad.ActualRadialWords
