import AKC9ReservedMatrixDecay

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
open Set
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.BoundaryLift Grad.AnnularKernelL2
open Grad.AnnularReconstruction Grad.AnnularKernelContinuity

theorem latticeDoubleDecay_summable :
    Summable (fun index : (ℤ × ℤ) × (ℤ × ℤ) =>
      (annularFrequency index.1.1 index.1.2 ^ 4)⁻¹ * (annularFrequency index.2.1 index.2.2 ^ 4)⁻¹) :=
  fullLattice_decay_summable.mul_of_nonneg fullLattice_decay_summable
    (fun mode => inv_nonneg.mpr (pow_nonneg (annularFrequency_pos mode).le _))
    (fun mode => inv_nonneg.mpr (pow_nonneg (annularFrequency_pos mode).le _))

theorem conjugatedMatrixPoint_summable {source target : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (radius : RadialPoint) (kernel : RadialKernel parameters radius source target) :
    Summable (conjugatedMatrixPoint parameters grade 4 radius kernel) := by
  apply Summable.of_norm_bounded (latticeDoubleDecay_summable.mul_left
    (fullKernelMoment (radialKernelParameters parameters radius) (grade + 4) kernel))
  intro index
  simpa only [mul_assoc] using conjugatedMatrixPoint_bound parameters grade 4 4 radius kernel
    (fullKernelMoment (radialKernelParameters parameters radius) (grade + 4) kernel) le_rfl index

/-- Absolute convergence of the matrix entries represents precisely the
accepted original weighted kernel, including every input-dependent entry. -/
theorem conjugatedKernelAction_matrixSeries {source target : ℕ} (parameters : PhaseParameters)
    (grade reserve : ℕ) (radius : RadialPoint) (kernel : RadialKernel parameters radius source target)
    (summable : Summable (conjugatedMatrixPoint parameters grade reserve radius kernel)) :
    conjugatedKernelAction parameters grade reserve radius kernel =
      ∑' index, conjugatedMatrixPoint parameters grade reserve radius kernel index := by
  apply ContinuousLinearMap.ext
  intro field
  apply lp.ext
  funext mode
  have observed := (lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean target) 2 mode).hasSum
    ((operatorEvaluation parameters 0 field).hasSum summable.hasSum)
  have fibers : ∀ shift : ℤ × ℤ, HasSum
      (fun input => conjugatedMatrixPoint parameters grade reserve radius kernel (shift, input) field mode)
      (((bulkWeightRatio parameters grade radius.val shift mode : ℂ) *
        frequencyReserveSymbol reserve (twoFrequencyTranslation shift mode)) •
          kernel.entry shift (twoFrequencyTranslation shift mode) (field (twoFrequencyTranslation shift mode))) := by
    intro shift
    apply (hasSum_ite_eq (twoFrequencyTranslation shift mode) _).congr_fun
    intro input
    rw [conjugatedMatrixPoint, fourierMatrixPoint_coordinate]
    by_cases same : input = twoFrequencyTranslation shift mode
    · subst input
      simp only [Equiv.symm_apply_apply, ite_true, smul_apply]
    · have different : mode ≠ (twoFrequencyTranslation shift).symm input := by
        intro equal
        apply same
        rw [equal, Equiv.apply_symm_apply]
      simp only [same, different, ite_false]
  exact (conjugatedKernelAction_coefficient parameters grade reserve radius kernel field mode).unique
    (observed.prod_fiberwise fibers)

end Grad.AnnularWeightedSmoothness
