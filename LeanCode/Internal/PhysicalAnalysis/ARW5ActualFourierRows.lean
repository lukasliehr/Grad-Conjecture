import ARW3PolarWordIdentity
import ARW4ActualOuterGerm

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators
namespace Grad.ActualRadialWords
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.ActualOuterCollar Grad.CollarCartesian Grad.BoundaryLift Grad.BoundaryTrace

def wordAmplitude {order : ℕ} (mode : ℤ) (profile : ℝ → ComplexEuclidean 1)
    (word : CartesianWord order) (time : ℝ) : ComplexEuclidean 1 :=
  wordFactor mode word • iteratedDerivWithin (wordCount word 0) profile (Icc (1 / 2 : ℝ) 1) (1 - time)

theorem wordAmplitude_continuousOn {order : ℕ} (mode : ℤ) (profile : ℝ → ComplexEuclidean 1)
    (smooth : ContDiffOn ℝ ∞ profile (Icc (1 / 2 : ℝ) 1)) (word : CartesianWord order) :
    ContinuousOn (wordAmplitude mode profile word) (Icc (0 : ℝ) (1 / 2)) := by
  change ContinuousOn ((fun _ : ℝ => wordFactor mode word) •
    (fun time => iteratedDerivWithin (wordCount word 0) profile (Icc (1 / 2 : ℝ) 1) (1 - time))) _
  apply continuousOn_const.smul
  apply (smooth.continuousOn_iteratedDerivWithin
    (by exact_mod_cast (le_top : (wordCount word 0 : ℕ∞) ≤ ⊤))
    (uniqueDiffOn_Icc (by norm_num : (1 / 2 : ℝ) < 1))).comp
      (continuousOn_const.sub continuousOn_id)
  intro time inside
  change (1 / 2 : ℝ) ≤ 1 - time ∧ 1 - time ≤ 1
  constructor <;> linarith [inside.1, inside.2]

theorem wordFactor_norm {order : ℕ} (mode : ℤ) (word : CartesianWord order) :
    ‖wordFactor mode word‖ = |(mode : ℝ)| ^ wordCount word 1 := by
  simp [wordFactor, norm_pow]

theorem wordAmplitude_norm_sq {order : ℕ} (mode : ℤ) (profile : ℝ → ComplexEuclidean 1)
    (word : CartesianWord order) (time : ℝ) :
    ‖wordAmplitude mode profile word time‖ ^ 2 =
      |(mode : ℝ)| ^ (2 * wordCount word 1) *
        ‖iteratedDerivWithin (wordCount word 0) profile (Icc (1 / 2 : ℝ) 1) (1 - time)‖ ^ 2 := by
  rw [wordAmplitude, norm_smul, wordFactor_norm, mul_pow, ← pow_mul]
  congr 2
  omega

def actualWordRows (parameter : ℝ) (source : highDiskL2) (order : ℕ)
    (word : CartesianWord order) (mode : ℤ) (time : ℝ) : ComplexEuclidean 1 :=
  if mode ∉ lowAngularModes then wordAmplitude mode (actualProfile mode parameter source) word time else 0

theorem actualWordRows_continuousOn (parameter : ℝ) (source : highDiskL2)
    (core : ClosedJet 1) (same : source.val = closedL2Core core) (order : ℕ)
    (word : CartesianWord order) (mode : ℤ) :
    ContinuousOn (actualWordRows parameter source order word mode) (Icc (0 : ℝ) (1 / 2)) := by
  change ContinuousOn (fun time => if mode ∉ lowAngularModes then
    wordAmplitude mode (actualProfile mode parameter source) word time else 0) _
  by_cases high : mode ∉ lowAngularModes
  · simp only [high]
    exact wordAmplitude_continuousOn mode _ (actualProfile_smooth mode high parameter source core same) word
  · simp only [high, if_false]
    exact continuousOn_const

theorem actualPolarFinite_word_expansion (modes : Finset ℤ) (parameter : ℝ) (source : highDiskL2)
    (core : ClosedJet 1) (same : source.val = closedL2Core core)
    (order : ℕ) (word : CartesianWord order) (point : ℝ × ℝ) (inside : point ∈ openHalfCollar) :
    iteratedFDeriv ℝ order (actualPolarFinite modes parameter source) point
      (fun position => productBasis (word position)) =
      ∑ mode ∈ finiteHighModes modes, fourier mode (point.2 : CellCircle) •
        actualWordRows parameter source order word mode point.1 := by
  rw [actualPolarFinite, iteratedFDeriv_sum_apply]
  · rw [sum_apply]
    apply Finset.sum_congr rfl
    intro mode member
    have high := (Finset.mem_filter.mp member).2
    rw [polarMode_word_derivative mode _ (actualProfile_smooth mode high parameter source core same),
      actualWordRows, if_pos high, wordAmplitude, polarRadialDerivative,
      show fourier mode (point.2 : CellCircle) = cellExponential mode point.2 from cellCharacter_coe _ _]
    · exact smul_comm _ _ _
    · exact inside
  · intro mode member
    exact ((polarMode_smoothOn mode _ (actualProfile_smooth mode (Finset.mem_filter.mp member).2
      parameter source core same)).contDiffAt (openHalfCollar_open.mem_nhds inside)).of_le
        (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))

end Grad.ActualRadialWords
