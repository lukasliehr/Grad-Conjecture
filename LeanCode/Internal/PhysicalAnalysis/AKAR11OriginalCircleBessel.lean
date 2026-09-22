import AKAR10SixCoefficientNorms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.BoundaryTrace
open Grad.SourceCollarCoefficients
open Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.PhaseAlgebra Grad.BoundaryLift

variable {dimension : ℕ}

theorem finite_circle_family_bessel (field : ℤ → ℝ → ComplexEuclidean dimension)
    (continuousField : ∀ cell, Continuous (field cell)) (constant : ℝ)
    (energy : ∀ cells : Finset ℤ, ∀ angle, ∑ cell ∈ cells, ‖field cell angle‖^2 ≤ constant^2)
    (modes cells : Finset ℤ) :
    ∑ cell ∈ cells, ∑ mode ∈ modes, ‖angularCoefficient (field cell) mode‖^2 ≤ constant^2 := by
  have bessel := Finset.sum_le_sum (s := cells) (fun cell _ => angular_bessel_finite (field cell) (continuousField cell) modes)
  have integrable (cell : ℤ) : IntervalIntegrable (fun angle => ‖field cell angle‖^2) volume (-Real.pi) Real.pi :=
    ((continuousField cell).norm.pow 2).intervalIntegrable _ _
  have continuousEnergy : Continuous (fun angle => ∑ cell ∈ cells, ‖field cell angle‖^2) := by
    fun_prop
  have integral := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun angle => ∑ cell ∈ cells, ‖field cell angle‖^2) (g := fun _ => constant^2)
    (neg_lt_self Real.pi_pos).le (continuousEnergy.intervalIntegrable _ _)
    intervalIntegrable_const (fun angle _ => energy cells angle)
  have averaged := mul_le_mul_of_nonneg_left integral (by positivity : 0 ≤ (2*Real.pi)⁻¹)
  rw [intervalIntegral.integral_const,smul_eq_mul] at averaged
  have cancel : (2*Real.pi)⁻¹*((Real.pi- -Real.pi)*constant^2)=constant^2 := by
    rw [show Real.pi- -Real.pi=2*Real.pi by ring,← mul_assoc,inv_mul_cancel₀ (by positivity : 2*Real.pi≠0),one_mul]
  rw [cancel] at averaged
  rw [← Finset.mul_sum,← intervalIntegral.integral_finsetSum (fun cell _ => integrable cell)] at bessel
  exact bessel.trans (by simpa only [Finset.mul_sum] using averaged)

theorem original_circle_family_finiteEnergy (field : ℤ → ℝ → ComplexEuclidean dimension)
    (continuousField : ∀ cell, Continuous (field cell)) (constant : ℝ)
    (energy : ∀ cells : Finset ℤ, ∀ angle, ∑ cell ∈ cells, ‖field cell angle‖^2 ≤ constant^2)
    (modes : Finset (ℤ × ℤ)) :
    ∑ mode ∈ modes, ‖angularCoefficient (field mode.2) mode.1‖^2 ≤ constant^2 := by
  have subset : modes ⊆ (modes.image Prod.fst) ×ˢ (modes.image Prod.snd) := by
    intro mode inside
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨mode,inside,rfl⟩,Finset.mem_image.mpr ⟨mode,inside,rfl⟩⟩
  apply (Finset.sum_le_sum_of_subset_of_nonneg subset (fun _ _ _ => sq_nonneg _)).trans
  rw [Finset.sum_product,Finset.sum_comm]
  exact finite_circle_family_bessel field continuousField constant energy _ _

theorem original_circle_family_memlp (field : ℤ → ℝ → ComplexEuclidean dimension)
    (continuousField : ∀ cell, Continuous (field cell)) (constant : ℝ)
    (energy : ∀ cells : Finset ℤ, ∀ angle, ∑ cell ∈ cells, ‖field cell angle‖^2 ≤ constant^2) :
    Memℓp (fun mode : ℤ × ℤ => angularCoefficient (field mode.2) mode.1) 2 := by
  apply (memℓp_gen_iff (p := 2) (by norm_num)).mpr
  simp only [ENNReal.toReal_ofNat,Real.rpow_two]
  exact summable_of_sum_le (fun _ => sq_nonneg _) (original_circle_family_finiteEnergy field continuousField constant energy)

def originalCircleFamilyVector (field : ℤ → ℝ → ComplexEuclidean dimension)
    (continuousField : ∀ cell, Continuous (field cell)) (constant : ℝ)
    (energy : ∀ cells : Finset ℤ, ∀ angle, ∑ cell ∈ cells, ‖field cell angle‖^2 ≤ constant^2) : CellL2 dimension :=
  ⟨_,original_circle_family_memlp field continuousField constant energy⟩

theorem originalCircleFamilyVector_bound (field : ℤ → ℝ → ComplexEuclidean dimension)
    (continuousField : ∀ cell, Continuous (field cell)) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (energy : ∀ cells : Finset ℤ, ∀ angle, ∑ cell ∈ cells, ‖field cell angle‖^2 ≤ constant^2) :
    ‖originalCircleFamilyVector field continuousField constant energy‖ ≤ constant := by
  apply lp.norm_le_of_forall_sum_le (p := 2) (by norm_num) nonnegative
  intro modes
  simpa only [originalCircleFamilyVector,ENNReal.toReal_ofNat,Real.rpow_two] using
    original_circle_family_finiteEnergy field continuousField constant energy modes

end Grad.OriginalKernelRetainedDecay
