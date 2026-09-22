import ARC11LocalCutoffCalculus

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff
namespace Grad.CollarCartesian
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints Grad.BoundaryLift

def openHalfCollar : Set (ℝ × ℝ) := Ioo (0 : ℝ) (1 / 2) ×ˢ univ

theorem openHalfCollar_open : IsOpen openHalfCollar := isOpen_Ioo.prod isOpen_univ

def mixedRowDensity {dimension : ℕ} (modes : Finset ℤ)
    (rows : (order : ℕ) → CartesianWord order → ℤ → ℝ → ComplexEuclidean dimension)
    (order : ℕ) (time : ℝ) : ℝ :=
  productWordCoefficientSum order * ∑ word : CartesianWord order,
    ‖productWordCoefficient word‖ * ∑ mode ∈ modes, ‖rows order word mode time‖ ^ 2

def mixedRowsDensity {dimension : ℕ} (modes : Finset ℤ)
    (rows : (order : ℕ) → CartesianWord order → ℤ → ℝ → ComplexEuclidean dimension)
    (grade : ℕ) (time : ℝ) : ℝ :=
  (2 * Real.pi) * ∑ order ∈ Finset.range (grade + 1), mixedRowDensity modes rows order time

theorem mixedRowsDensity_continuous {dimension : ℕ} (modes : Finset ℤ)
    (rows : (order : ℕ) → CartesianWord order → ℤ → ℝ → ComplexEuclidean dimension)
    (rowsContinuous : ∀ order word mode, Continuous (rows order word mode)) (grade : ℕ) :
    Continuous (mixedRowsDensity modes rows grade) := by
  apply continuous_const.mul
  apply continuous_finsetSum
  intro order _
  apply continuous_const.mul
  apply continuous_finsetSum
  intro word _
  apply continuous_const.mul
  apply continuous_finsetSum
  intro mode _
  exact (rowsContinuous order word mode).norm.pow 2

theorem mixedRowsDensity_continuousOn {dimension : ℕ} (modes : Finset ℤ)
    (rows : (order : ℕ) → CartesianWord order → ℤ → ℝ → ComplexEuclidean dimension)
    (rowsContinuous : ∀ order word mode, ContinuousOn (rows order word mode) (Icc (0 : ℝ) (1 / 2)))
    (grade : ℕ) : ContinuousOn (mixedRowsDensity modes rows grade) (Icc (0 : ℝ) (1 / 2)) := by
  apply continuousOn_const.mul
  apply continuousOn_finsetSum
  intro order _
  apply continuousOn_const.mul
  apply continuousOn_finsetSum
  intro word _
  apply continuousOn_const.mul
  apply continuousOn_finsetSum
  intro mode _
  exact (rowsContinuous order word mode).norm.pow 2

theorem localPolarTensor_continuous_angle {dimension : ℕ}
    (polar : ℝ × ℝ → ComplexEuclidean dimension) (smooth : ContDiffOn ℝ ∞ polar openHalfCollar)
    (order : ℕ) (time : ℝ) (timeIn : time ∈ Ioo (0 : ℝ) (1 / 2)) :
    Continuous (fun angle : ℝ => iteratedFDeriv ℝ order polar (time, angle)) := by
  rw [continuous_iff_continuousAt]
  intro angle
  have member : (time, angle) ∈ openHalfCollar := ⟨timeIn, mem_univ _⟩
  exact ((smooth.contDiffAt (openHalfCollar_open.mem_nhds member)).continuousAt_iteratedFDeriv
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).comp
      (continuous_const.prodMk continuous_id).continuousAt

theorem localPolarDensity_angular_bound {dimension : ℕ}
    (polar : ℝ × ℝ → ComplexEuclidean dimension) (smooth : ContDiffOn ℝ ∞ polar openHalfCollar)
    (modes : Finset ℤ)
    (rows : (order : ℕ) → CartesianWord order → ℤ → ℝ → ComplexEuclidean dimension)
    (grade : ℕ) (time : ℝ) (timeIn : time ∈ Ioo (0 : ℝ) (1 / 2))
    (expansion : ∀ order, order ≤ grade → ∀ angle word,
      iteratedFDeriv ℝ order polar (time, angle) (fun position => productBasis (word position)) =
        ∑ mode ∈ modes, fourier mode (angle : CellCircle) • rows order word mode time) :
    (∫ angle in -Real.pi..Real.pi, polarJetSquaredDensity polar grade (time, angle)) ≤
      mixedRowsDensity modes rows grade time := by
  rw [show (fun angle => polarJetSquaredDensity polar grade (time, angle)) =
      (fun angle => ∑ order ∈ Finset.range (grade + 1), ‖iteratedFDeriv ℝ order polar (time, angle)‖ ^ 2) by rfl,
    intervalIntegral.integral_finsetSum, mixedRowsDensity, Finset.mul_sum]
  · apply Finset.sum_le_sum
    intro order orderIn
    have comparison := finiteTensorRows_integral _
      (localPolarTensor_continuous_angle polar smooth order time timeIn) modes
      (fun word mode => rows order word mode time)
      (expansion order (by have := Finset.mem_range.mp orderIn; omega))
    exact comparison.trans_eq (by unfold mixedRowDensity; ring)
  · intro order _
    exact ((localPolarTensor_continuous_angle polar smooth order time timeIn).norm.pow 2).intervalIntegrable _ _

end Grad.CollarCartesian
