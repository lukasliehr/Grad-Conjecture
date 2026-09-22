import AKC2FaithfulConjugatedAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 220000
open Set
open scoped Topology BigOperators
namespace Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.BoundaryLift Grad.AnnularKernelL2
open Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.PhaseAlgebra

theorem hilbertReserve_zero (parameters : PhaseParameters) (dimension : ℕ) :
    hilbertReserve parameters dimension 0 = ContinuousLinearMap.id ℂ (CellL2 dimension) := by
  apply ContinuousLinearMap.ext
  intro field
  apply lp.ext
  funext mode
  rw [hilbertReserve_apply, frequencyReserveSymbol, pow_zero, inv_one, one_smul]
  rfl

theorem hilbertReserve_add (parameters : PhaseParameters) (dimension first second : ℕ) :
    hilbertReserve parameters dimension (first + second) =
      (hilbertReserve parameters dimension first).comp (hilbertReserve parameters dimension second) := by
  apply ContinuousLinearMap.ext
  intro field
  apply lp.ext
  funext mode
  change frequencyReserveSymbol (first + second) mode • field mode =
    frequencyReserveSymbol first mode • (frequencyReserveSymbol second mode • field mode)
  rw [frequencyReserveSymbol, frequencyReserveSymbol, frequencyReserveSymbol, pow_add, mul_inv, smul_smul]

theorem bulkWeightRatio_reserve (parameters : PhaseParameters) (grade reserve : ℕ)
    (radius : ℝ) (shift mode : ℤ × ℤ) :
    (bulkWeightRatio parameters grade radius shift mode : ℂ) * frequencyReserveSymbol reserve (twoFrequencyTranslation shift mode) =
      frequencyReserveSymbol reserve mode * (bulkWeightRatio parameters (grade + reserve) radius shift mode : ℂ) := by
  unfold bulkWeightRatio frequencyReserveSymbol
  push_cast
  rw [pow_add, pow_add]
  field_simp [(show (annularFrequency mode.1 mode.2 : ℂ) ≠ 0 from
    by exact_mod_cast (Grad.SourceBoundaryTrace.annularFrequency_pos mode).ne')]

/-- The SAME action at every grade respects the literal reserve inclusions. -/
theorem bulkKernelAction_reserve {source target : ℕ} (parameters : PhaseParameters)
    (grade reserve : ℕ) (radius : RadialPoint) (kernel : RadialKernel parameters radius source target) :
    (bulkKernelAction parameters grade radius kernel).comp (hilbertReserve parameters source reserve) =
      (hilbertReserve parameters target reserve).comp (bulkKernelAction parameters (grade + reserve) radius kernel) := by
  apply ContinuousLinearMap.ext
  intro field
  apply lp.ext
  funext mode
  change conjugatedKernelAction parameters grade reserve radius kernel field mode =
    frequencyReserveSymbol reserve mode • bulkKernelAction parameters (grade + reserve) radius kernel field mode
  have higher := (frequencyReserveSymbol reserve mode • ContinuousLinearMap.id ℂ (ComplexEuclidean target)).hasSum
    (bulkKernelAction_coordinate parameters (grade + reserve) radius kernel field mode)
  apply (conjugatedKernelAction_coefficient parameters grade reserve radius kernel field mode).unique
  apply higher.congr_fun
  intro shift
  change ((bulkWeightRatio parameters grade radius.val shift mode : ℂ) *
    frequencyReserveSymbol reserve (twoFrequencyTranslation shift mode)) •
      kernel.entry shift (twoFrequencyTranslation shift mode) (field (twoFrequencyTranslation shift mode)) =
    frequencyReserveSymbol reserve mode • ((bulkWeightRatio parameters (grade + reserve) radius.val shift mode : ℂ) •
      kernel.entry shift (twoFrequencyTranslation shift mode) (field (twoFrequencyTranslation shift mode)))
  rw [smul_smul, bulkWeightRatio_reserve]

end Grad.AnnularWeightedSmoothness
