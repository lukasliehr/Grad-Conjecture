import AKC1SameConjugatedKernelAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
open Set
open scoped Topology BigOperators
namespace Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.BoundaryLift Grad.AnnularKernelL2
open Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.AnnularRadialSmoothness Grad.PhaseAlgebra

theorem inversePhase_bound (parameters : PhaseParameters) (radius : RadialPoint) (mode : ℤ × ℤ) :
    ‖(Real.exp (-radialPhase parameters radius.val mode.2) : ℂ)‖ ≤ 1 := by
  have one : 1 ≤ phaseWeight parameters radius.val mode.2 :=
    Real.one_le_exp_iff.mpr (mul_nonneg
      (phaseWidth_nonneg parameters radius.val radius.property.1 radius.property.2) (abs_nonneg _))
  have phase := Real.one_le_exp_iff.mp (one.trans
    (phaseWeight_le_exp_radialPhase parameters radius.val radius.property.1 radius.property.2 mode.2))
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr phase)

def phaseObservation (parameters : PhaseParameters) (radius : RadialPoint) (dimension : ℕ) :
    CellL2 dimension →L[ℂ] CellL2 dimension :=
  boundedHilbertMultiplier parameters dimension (fun mode => (Real.exp (-radialPhase parameters radius.val mode.2) : ℂ))
    1 zero_le_one (inversePhase_bound parameters radius)

theorem phaseObservation_apply (parameters : PhaseParameters) (radius : RadialPoint) (dimension : ℕ)
    (field : CellL2 dimension) (mode : ℤ × ℤ) :
    phaseObservation parameters radius dimension field mode =
      (Real.exp (-radialPhase parameters radius.val mode.2) : ℂ) • field mode := rfl

theorem phaseObservation_injective (parameters : PhaseParameters) (radius : RadialPoint) (dimension : ℕ) :
    Function.Injective (phaseObservation parameters radius dimension) := by
  intro first second same
  apply lp.ext
  funext mode
  have point := congrArg (fun field : CellL2 dimension => field mode) same
  exact smul_right_injective (ComplexEuclidean dimension)
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne') point

theorem phaseRatio_cancel (parameters : PhaseParameters) (grade : ℕ) (radius : ℝ) (shift mode : ℤ × ℤ) :
    (Real.exp (-radialPhase parameters radius mode.2) : ℂ) * (bulkWeightRatio parameters grade radius shift mode : ℂ) =
      (polynomialWeightRatio grade shift mode : ℂ) *
        (Real.exp (-radialPhase parameters radius (twoFrequencyTranslation shift mode).2) : ℂ) := by
  unfold bulkWeightRatio polynomialWeightRatio
  rw [Real.exp_sub, Real.exp_neg, Real.exp_neg]
  push_cast
  field_simp [(Real.exp_pos (radialPhase parameters radius mode.2)).ne']

/-- Faithful observation intertwines the SAME weighted and polynomial actions.
It will only transfer already accepted algebra and inverse identities. -/
theorem phaseObservation_kernel {source target : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (radius : RadialPoint) (kernel : RadialKernel parameters radius source target)
    (field : CellL2 source) :
    phaseObservation parameters radius target (bulkKernelAction parameters grade radius kernel field) =
      polynomialKernelAction (radialKernelParameters parameters radius) grade kernel
        (phaseObservation parameters radius source field) := by
  apply lp.ext
  funext mode
  rw [phaseObservation_apply]
  have weighted := ((Real.exp (-radialPhase parameters radius.val mode.2) : ℂ) •
    ContinuousLinearMap.id ℂ (ComplexEuclidean target)).hasSum
      (bulkKernelAction_coordinate parameters grade radius kernel field mode)
  have plain := polynomialKernelAction_coefficient (radialKernelParameters parameters radius) grade kernel
    (phaseObservation parameters radius source field) mode
  apply weighted.unique
  apply plain.congr_fun
  intro shift
  change (Real.exp (-radialPhase parameters radius.val mode.2) : ℂ) •
    ((bulkWeightRatio parameters grade radius.val shift mode : ℂ) •
      kernel.entry shift (twoFrequencyTranslation shift mode) (field (twoFrequencyTranslation shift mode))) =
    (polynomialWeightRatio grade shift mode : ℂ) •
      kernel.entry shift (twoFrequencyTranslation shift mode)
        ((Real.exp (-radialPhase parameters radius.val (twoFrequencyTranslation shift mode).2) : ℂ) •
          field (twoFrequencyTranslation shift mode))
  rw [map_smul, smul_smul, smul_smul, phaseRatio_cancel]

theorem bulkKernelAction_composition {source middle target : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (radius : RadialPoint) (outer : RadialKernel parameters radius middle target)
    (inner : RadialKernel parameters radius source middle) :
    bulkKernelAction parameters grade radius (fullKernelComposition outer inner) =
      (bulkKernelAction parameters grade radius outer).comp (bulkKernelAction parameters grade radius inner) := by
  apply ContinuousLinearMap.ext
  intro field
  apply phaseObservation_injective parameters radius target
  rw [phaseObservation_kernel, polynomialKernelAction_comp]
  change polynomialKernelAction _ grade outer (polynomialKernelAction _ grade inner (phaseObservation parameters radius source field)) =
    phaseObservation parameters radius target (bulkKernelAction parameters grade radius outer (bulkKernelAction parameters grade radius inner field))
  rw [phaseObservation_kernel, phaseObservation_kernel]

theorem bulkKernelAction_identity (parameters : PhaseParameters) (grade : ℕ) (radius : RadialPoint) (dimension : ℕ) :
    bulkKernelAction parameters grade radius (fullIdentityKernel (radialKernelParameters parameters radius) dimension) =
      ContinuousLinearMap.id ℂ (CellL2 dimension) := by
  apply ContinuousLinearMap.ext
  intro field
  apply phaseObservation_injective parameters radius dimension
  rw [phaseObservation_kernel, polynomialKernelAction_identity]
  rfl

theorem bulkKernelAction_add {source target : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (radius : RadialPoint) (first second : RadialKernel parameters radius source target) :
    bulkKernelAction parameters grade radius (fullKernelAdd first second) =
      bulkKernelAction parameters grade radius first + bulkKernelAction parameters grade radius second := by
  apply ContinuousLinearMap.ext
  intro field
  apply phaseObservation_injective parameters radius target
  change phaseObservation parameters radius target (bulkKernelAction parameters grade radius (fullKernelAdd first second) field) =
    phaseObservation parameters radius target (bulkKernelAction parameters grade radius first field + bulkKernelAction parameters grade radius second field)
  rw [phaseObservation_kernel, polynomialKernelAction_add, map_add, phaseObservation_kernel, phaseObservation_kernel]
  rfl

theorem bulkKernelAction_smul {source target : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (radius : RadialPoint) (scalar : ℂ) (kernel : RadialKernel parameters radius source target) :
    bulkKernelAction parameters grade radius (fullKernelSmul scalar kernel) = scalar • bulkKernelAction parameters grade radius kernel := by
  apply ContinuousLinearMap.ext
  intro field
  apply phaseObservation_injective parameters radius target
  change phaseObservation parameters radius target (bulkKernelAction parameters grade radius (fullKernelSmul scalar kernel) field) =
    phaseObservation parameters radius target (scalar • bulkKernelAction parameters grade radius kernel field)
  rw [phaseObservation_kernel, polynomialKernelAction_smul, map_smul, phaseObservation_kernel]
  rfl

/-- Both original inverse laws at the same analytic width and every grade;
no high-grade smallness or replacement inverse appears. -/
theorem bulkKernelAction_inverse {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (radius : RadialPoint) (kernel : RadialKernel parameters radius dimension dimension)
    (low : ℝ) (bounded : fullKernelMoment (radialKernelParameters parameters radius) 0 kernel ≤ low) (small : low < 1) :
    let forward := bulkKernelAction parameters grade radius (fullKernelNegativeIdentityPerturbation (radialKernelParameters parameters radius) kernel)
    let inverse := bulkKernelAction parameters grade radius (fullKernelNegativeIdentityInverse (radialKernelParameters parameters radius) kernel low bounded small)
    forward.comp inverse = ContinuousLinearMap.id ℂ (CellL2 dimension) ∧
      inverse.comp forward = ContinuousLinearMap.id ℂ (CellL2 dimension) := by
  dsimp only
  constructor
  · rw [← bulkKernelAction_composition, fullKernelNegativeIdentity_inverse_right, bulkKernelAction_identity]
  · rw [← bulkKernelAction_composition, fullKernelNegativeIdentity_inverse_left, bulkKernelAction_identity]

end Grad.AnnularWeightedSmoothness
