import AKR20ActualTupleConjugatedRadialDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularOriginalSmoothCore Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.PhaseAlgebra
open Grad.AnnularOriginalHigh Grad.AnnularOriginalLow Grad.AnnularLowEnergy Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.WeightedTrace

open Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger

open Grad.AnnularCurrentLow Grad.AnnularCurrentSource Grad.AnnularHighTilt

variable (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (curve : ℕ → ℝ → CellL2 1)
    (continuous : ∀ grade, ContinuousOn (curve grade) (Icc lower 1))

def coherentHilbertSection (grade : ℕ) : C(Icc lower (1 : ℝ),CellL2 1) :=
  ⟨fun radius => curve grade radius.val,continuousOn_iff_continuous_domRestrict.mp (continuous grade)⟩

def coherentCoefficientSection (grade : ℕ) (mode : ℤ × ℤ) : RadialContinuousSection 1 lower :=
  ⟨fun radius => curve grade radius.val mode,
    (lp.evalCLM ℝ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 mode).continuous.comp
      (coherentHilbertSection lower curve continuous grade).continuous⟩

variable (same : ∀ grade radius, radius ∈ Icc lower 1 → ∀ mode : ℤ × ℤ,
  curve grade radius mode = ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) • curve 0 radius mode)

include same in
theorem coherentCoefficientSection_summable :
    Summable (fun mode : ℤ × ℤ => ‖coherentCoefficientSection lower curve continuous 0 mode‖) := by
  let bound := ‖coherentHilbertSection lower curve continuous 4‖
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun mode => ?_)
    (Grad.AnnularJointRegularity.annularLattice_inverse_four_summable.mul_left bound)
  have gradeLaw : coherentCoefficientSection lower curve continuous 4 mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ 4 : ℝ) : ℂ) •
        coherentCoefficientSection lower curve continuous 0 mode := by
    apply ContinuousMap.ext
    intro radius
    exact same 4 radius.val radius.property mode
  have normBound : ‖coherentCoefficientSection lower curve continuous 4 mode‖ ≤ bound := by
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro radius
    exact (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (curve 4 radius.val) mode).trans
      ((coherentHilbertSection lower curve continuous 4).norm_coe_le_norm radius)
  rw [gradeLaw,norm_smul,Complex.norm_real] at normBound
  rw [Real.norm_of_nonneg (by unfold Grad.AnnularVariational.annularFrequency; positivity)] at normBound
  change _ ≤ bound * (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ 4)⁻¹
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos (Grad.SourceBoundaryTrace.annularFrequency_pos mode) 4)).mpr
  exact (mul_comm _ _).trans_le normBound

include same in
theorem coherentSqrtStored_summable :
    Summable (fun mode : ℤ × ℤ => ‖radialSqrtMap 1 lower
      (radialSectionL2 1 lower positive bounded.le (coherentCoefficientSection lower curve continuous 0 mode))‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun mode => ?_)
    ((coherentCoefficientSection_summable lower curve continuous same).mul_left ‖radialSqrtMap 1 lower‖)
  have bound := radialSectionL2Linear_bound 1 lower positive bounded.le
    (coherentCoefficientSection lower curve continuous 0 mode)
  exact ((radialSqrtMap 1 lower).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (by simpa only [radialSectionL2,LinearMap.mkContinuous_apply,one_mul] using bound) (norm_nonneg _))

/-- The original un-tilted full bulk norm of a coherent all-grade Hilbert
curve, with exactly the sqrt(r) storage required by the source norm. -/
def coherentOriginalBulk : DivisionRow 1 lower :=
  ⟨fun mode => radialSqrtMap 1 lower
    (radialSectionL2 1 lower positive bounded.le (coherentCoefficientSection lower curve continuous 0 mode)), by
    have one : Memℓp (fun mode : ℤ × ℤ => radialSqrtMap 1 lower
        (radialSectionL2 1 lower positive bounded.le (coherentCoefficientSection lower curve continuous 0 mode))) 1 := by
      apply memℓp_gen
      simpa only [ENNReal.toReal_one,Real.rpow_one] using coherentSqrtStored_summable lower positive bounded curve continuous same
    exact one.of_exponent_ge (by norm_num)⟩

theorem coherentOriginalBulk_physical (parameters : PhaseParameters)
    (physical : Icc lower (1 : ℝ) → (ℤ × ℤ) → ComplexEuclidean 1)
    (baseSame : ∀ radius : Icc lower (1 : ℝ), ∀ mode,
      curve 0 radius.val mode = (Real.exp (radialPhase parameters radius.val mode.2) : ℂ) • physical radius mode) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ mode,
      originalF1Coefficient parameters lower positive bounded.le
        (coherentOriginalBulk lower positive bounded curve continuous same) radius mode = physical ⟨radius,inside⟩ mode := by
  have representatives (mode : ℤ × ℤ) := radialSectionL2_ae 1 lower positive bounded.le
    (coherentCoefficientSection lower curve continuous 0 mode)
  have square (mode : ℤ × ℤ) := radialSqrtMap_ae 1 lower
    (radialSectionL2 1 lower positive bounded.le (coherentCoefficientSection lower curve continuous 0 mode))
  filter_upwards [divisionHighWeight_ae lower positive bounded.le (coherentOriginalBulk lower positive bounded curve continuous same),
    (ae_all_iff.mpr representatives),(ae_all_iff.mpr square)] with radius high value sqrtStored
  intro inside mode
  unfold originalF1Coefficient lowRhoPhysicalCoefficient
  rw [high mode]
  change _ • (((radius ^ (-9/4 : ℝ) : ℝ) : ℂ) • (radialSqrtMap 1 lower
    (radialSectionL2 1 lower positive bounded.le (coherentCoefficientSection lower curve continuous 0 mode))) radius) = _
  rw [sqrtStored mode,← value mode,originalSourceStorage_decode parameters lower positive radius inside mode]
  change (Real.exp (-radialPhase parameters radius mode.2) : ℂ) • curve 0 (radialClamp lower bounded.le radius).val mode = _
  rw [radialClamp_eq lower bounded.le radius inside,baseSame ⟨radius,inside⟩ mode,Real.exp_neg,Complex.ofReal_inv,
    inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')]

end Grad.AnnularOriginalCoreRealization
