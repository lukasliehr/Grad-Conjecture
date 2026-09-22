import AKBP32OriginalB10NativeStartup

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.TensorBootstrap Grad.SobolevBridge

abbrev StartupOrderedL2 (rank : ℕ) := PiLp 2 (fun _ : DerivativeIndex rank => FieldL2)
abbrev StartupOrderedH1 (rank : ℕ) := PiLp 2 (fun _ : DerivativeIndex rank => FieldH1)

def startupOrderedValue (rank : ℕ) : StartupOrderedH1 rank →L[ℂ] StartupOrderedL2 rank :=
  hilbertLift valueInclusion

def startupOrderedSecondSum (rank : ℕ)
    (kernels : TensorIndex → StartupOrderedL2 rank →L[ℂ] StartupOrderedL2 rank) :
    StartupOrderedL2 rank →L[ℂ] StartupOrderedL2 rank :=
  ∑ index : TensorIndex, (hilbertLift (startupSecondL2 index)).comp (kernels index)

theorem startupOrderedSecondSum_component (rank : ℕ)
    (kernels : TensorIndex → StartupOrderedL2 rank →L[ℂ] StartupOrderedL2 rank)
    (field : StartupOrderedL2 rank) (word : DerivativeIndex rank) :
    startupOrderedSecondSum rank kernels field word =
      ∑ index : TensorIndex, startupSecondL2 index (kernels index field word) := by
  simp only [startupOrderedSecondSum, sum_apply, ContinuousLinearMap.comp_apply]
  change (∑ index : TensorIndex, hilbertLift (startupSecondL2 index) (kernels index field)).ofLp word = _
  rw [WithLp.ofLp_sum]
  simp only [Finset.sum_apply, hilbertLift_apply]

/-- The coupled ordered-covector equation uses the existing scalar tensor
resolvents coordinatewise; the coefficient kernels may mix every word. -/
theorem startupOrdered_divDiv_resolvent (rank : ℕ)
    (kernels : TensorIndex → StartupOrderedL2 rank →L[ℂ] StartupOrderedL2 rank)
    (original zeroth : StartupOrderedL2 rank) (flux : Fin 2 → StartupOrderedL2 rank)
    (equation : ∀ word : DerivativeIndex rank,
      Laplacian.laplacian (distributionEmbedding (original word)) =
        (∑ index : TensorIndex, distributionDerivative index.1
          (distributionDerivative index.2 (distributionEmbedding (kernels index original word)))) +
        distributionEmbedding (zeroth word) +
        ∑ direction : Fin 2, distributionDerivative direction (distributionEmbedding (flux direction word))) :
    original + startupOrderedSecondSum rank kernels original =
      startupOrderedValue rank (WithLp.toLp 2 (fun word =>
        startupDivDivRemainder (original word) (zeroth word) (fun direction => flux direction word))) := by
  apply PiLp.ext
  intro word
  change original word + startupOrderedSecondSum rank kernels original word =
    valueInclusion (startupDivDivRemainder (original word) (zeroth word) (fun direction => flux direction word))
  rw [startupOrderedSecondSum_component]
  apply distributionEmbedding_injective
  rw [map_add, map_sum, startupDivDivRemainder_distribution]
  simp only [startupSecondL2_distribution, ← map_sum]
  have recovered := distributionResolvent_left (distributionEmbedding (original word))
  rw [equation word] at recovered
  have rearranged : distributionEmbedding (original word) -
      ((∑ index : TensorIndex, distributionDerivative index.1
        (distributionDerivative index.2 (distributionEmbedding (kernels index original word)))) +
        distributionEmbedding (zeroth word) +
        ∑ direction : Fin 2, distributionDerivative direction (distributionEmbedding (flux direction word))) =
      (distributionEmbedding (original word) - distributionEmbedding (zeroth word) -
        ∑ direction : Fin 2, distributionDerivative direction (distributionEmbedding (flux direction word))) -
      ∑ index : TensorIndex, distributionDerivative index.1
        (distributionDerivative index.2 (distributionEmbedding (kernels index original word))) := by abel
  rw [rearranged, map_sub] at recovered
  exact (sub_eq_iff_eq_add.mp recovered).symm

theorem startupCompatibleNeumann_same {Rough Regular : Type*}
    [NormedAddCommGroup Rough] [NormedSpace ℂ Rough] [CompleteSpace Rough]
    [NormedAddCommGroup Regular] [NormedSpace ℂ Regular] [CompleteSpace Regular]
    (inclusion : Regular →L[ℂ] Rough) (coarse : Rough →L[ℂ] Rough) (fine : Regular →L[ℂ] Regular)
    (compatible : ∀ field, inclusion (fine field) = coarse (inclusion field))
    (coarseSmall : ‖coarse‖ < 1) (fineSmall : ‖fine‖ < 1)
    (original : Rough) (remainder : Regular)
    (equation : original + coarse original = inclusion remainder) :
    ∃ improved : Regular, inclusion improved = original := by
  let candidate := Grad.Foundations.neumannInverse (𝕜 := ℂ) (X := Regular) (-fine) remainder
  have fineRight : candidate + fine candidate = remainder := by
    have same := congrArg (fun operator : Regular →L[ℂ] Regular => operator remainder)
      (Grad.Foundations.neumannInverse_right (𝕜 := ℂ) (X := Regular) (-fine) (by simpa using fineSmall))
    change candidate - (-fine) candidate = remainder at same
    simpa only [neg_apply, sub_neg_eq_add] using same
  have coarseLeft (field : Rough) :
      Grad.Foundations.neumannInverse (𝕜 := ℂ) (X := Rough) (-coarse) (field + coarse field) = field := by
    have same := congrArg (fun operator : Rough →L[ℂ] Rough => operator field)
      (Grad.Foundations.neumannInverse_left (𝕜 := ℂ) (X := Rough) (-coarse) (by simpa using coarseSmall))
    change Grad.Foundations.neumannInverse (𝕜 := ℂ) (X := Rough) (-coarse) (field - (-coarse) field) = field at same
    simpa only [neg_apply, sub_neg_eq_add] using same
  have candidateEquation : inclusion candidate + coarse (inclusion candidate) = inclusion remainder := by
    rw [← compatible, ← map_add, fineRight]
  have same := congrArg (fun field : Rough =>
      Grad.Foundations.neumannInverse (𝕜 := ℂ) (X := Rough) (-coarse) field)
    (candidateEquation.trans equation.symm)
  rw [coarseLeft, coarseLeft] at same
  exact ⟨candidate, same⟩

/-- H1 regularity for a genuinely coupled ordered derivative tuple. Smallness
is required only of the displayed leading operator, independently of rank. -/
theorem startupOrdered_sameField_h1 (rank : ℕ)
    (kernels : TensorIndex → StartupOrderedL2 rank →L[ℂ] StartupOrderedL2 rank)
    (regular : StartupOrderedH1 rank →L[ℂ] StartupOrderedH1 rank)
    (compatible : ∀ field, startupOrderedValue rank (regular field) =
      startupOrderedSecondSum rank kernels (startupOrderedValue rank field))
    (coarseSmall : ‖startupOrderedSecondSum rank kernels‖ < 1) (fineSmall : ‖regular‖ < 1)
    (original zeroth : StartupOrderedL2 rank) (flux : Fin 2 → StartupOrderedL2 rank)
    (equation : ∀ word : DerivativeIndex rank,
      Laplacian.laplacian (distributionEmbedding (original word)) =
        (∑ index : TensorIndex, distributionDerivative index.1
          (distributionDerivative index.2 (distributionEmbedding (kernels index original word)))) +
        distributionEmbedding (zeroth word) +
        ∑ direction : Fin 2, distributionDerivative direction (distributionEmbedding (flux direction word))) :
    ∃ improved : StartupOrderedH1 rank, startupOrderedValue rank improved = original := by
  refine startupCompatibleNeumann_same (Rough := StartupOrderedL2 rank) (Regular := StartupOrderedH1 rank) (startupOrderedValue rank) (startupOrderedSecondSum rank kernels) regular
    compatible coarseSmall ?_ original
    (WithLp.toLp 2 (fun word => startupDivDivRemainder (original word) (zeroth word) (fun direction => flux direction word)))
    (startupOrdered_divDiv_resolvent rank kernels original zeroth flux equation)
  exact fineSmall

end Grad.CartesianStartup
