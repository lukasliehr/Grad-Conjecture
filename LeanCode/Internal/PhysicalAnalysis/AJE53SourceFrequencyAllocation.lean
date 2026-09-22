import AJE47RealSourceGeneratorCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.AnnularOrbitGenerators Grad.AnnularKernelOrbit Grad.AnnularVariational
open Grad.GaugeCoefficients.Physical.Allocation

section Allocation
variable {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]

omit [IsScalarTower ℝ ℂ V] in
theorem sourceLp_lowerGenerator_bound (frequency : ι → ℝ) (mode : ι → ℤ)
    (oneLe : ∀ index, 1 ≤ frequency index) (modeBound : ∀ index, |(mode index : ℝ)| ≤ frequency index)
    (field weighted generator : lp (fun _ : ι => V) 2) (grade order : ℕ) (ordered : order ≤ grade)
    (weightedActual : ∀ index, weighted index = frequency index ^ grade • field index)
    (generatorActual : ∀ index, generator index = (Complex.I * (mode index : ℂ)) ^ order • field index) :
    ‖generator‖ ≤ ‖weighted‖ := by
  apply lp.norm_mono (by norm_num)
  intro index
  rw [generatorActual,weightedActual,norm_smul,norm_smul,
    Grad.AnnularLowOrbit.cellGeneratorFactor_norm,Real.norm_of_nonneg (pow_nonneg (zero_le_one.trans (oneLe index)) grade)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (pow_le_pow_left₀ (abs_nonneg _) (modeBound index) order).trans (pow_le_pow_right₀ (oneLe index) ordered)

/-- The augmented coefficient factor and complementary actual source
axis derivative obey one-high allocation in the original completed lp norm. -/
theorem sourceLp_augmented_oneHigh (parameters : PhaseParameters) (base : ACore parameters 3)
    (rho epsilon : ℝ) (frequency : ι → ℝ) (mode : ι → ℤ)
    (oneLe : ∀ index, 1 ≤ frequency index) (modeBound : ∀ index, |(mode index : ℝ)| ≤ frequency index)
    (field weighted generator : lp (fun _ : ι => V) 2) (grade order : ℕ)
    (gradePositive : 0 < grade) (ordered : order ≤ grade)
    (small : physicalBudget parameters base rho epsilon 8 ≤ 1)
    (weightedActual : ∀ index, weighted index = frequency index ^ grade • field index)
    (generatorActual : ∀ index, generator index = (Complex.I * (mode index : ℂ)) ^ (grade - order) • field index) :
    (1 + physicalBudget parameters base rho epsilon (8 + order)) * ‖generator‖ ≤
      (1 + physicalInterpolationConstant 8 grade) *
        (‖weighted‖ + physicalBudget parameters base rho epsilon (8 + grade) * ‖field‖) := by
  have generatorBound := sourceLp_lowerGenerator_bound frequency mode oneLe modeBound field weighted generator grade (grade - order)
    (Nat.sub_le _ _) weightedActual generatorActual
  have weightedComplex (index : ι) : weighted index = ((frequency index ^ grade : ℝ) : ℂ) • field index := by
    rw [weightedActual,RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have allocated := lp_complementary_oneHigh parameters base rho epsilon frequency mode
    (fun index => zero_lt_one.trans_le (oneLe index)) modeBound field weighted generator 8 grade order gradePositive ordered
    weightedComplex generatorActual
  have constantNonnegative : 0 ≤ physicalInterpolationConstant 8 grade :=
    zero_le_one.trans (physicalInterpolationConstant_one_le 8 grade)
  have lowBound : physicalBudget parameters base rho epsilon 8 * ‖weighted‖ ≤ ‖weighted‖ :=
    (mul_le_mul_of_nonneg_right small (norm_nonneg weighted)).trans_eq (one_mul _)
  have weightedBound : ‖weighted‖ ≤ ‖weighted‖ + physicalBudget parameters base rho epsilon (8 + grade) * ‖field‖ :=
    le_add_of_nonneg_right (mul_nonneg (physicalBudget_nonnegative _ _ _ _ _) (norm_nonneg field))
  have allocated' := allocated.trans (mul_le_mul_of_nonneg_left (add_le_add lowBound le_rfl) constantNonnegative)
  nlinarith only [generatorBound,weightedBound,allocated']
end Allocation

/-- Pure scalar summation keeps the original full carrier out of arithmetic elaboration. -/
theorem elevenSourceBounds (factor total C target a b c d e f g h i j k : ℝ)
    (nonnegative : 0 ≤ factor) (totalBound : total ≤ a+b+c+d+e+f+g+h+i+j+k)
    (ha : factor*a ≤ C*target) (hb : factor*b ≤ C*target) (hc : factor*c ≤ C*target)
    (hd : factor*d ≤ C*target) (he : factor*e ≤ C*target) (hf : factor*f ≤ C*target)
    (hg : factor*g ≤ C*target) (hh : factor*h ≤ C*target) (hi : factor*i ≤ C*target)
    (hj : factor*j ≤ C*target) (hk : factor*k ≤ C*target) : factor * total ≤ 11 * C * target := by
  have scaled := mul_le_mul_of_nonneg_left totalBound nonnegative
  linarith only [scaled,ha,hb,hc,hd,he,hf,hg,hh,hi,hj,hk]

end Grad.AnnularStrongOrbit
