import AAT16ExactSourceGradeCarrier

noncomputable section
set_option maxHeartbeats 1000000

open Set Filter
open scoped Topology

namespace Grad.AnnularGrades

open Grad.AnnularVariational Grad.CartesianState

section Consumer
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (collar : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem annularInverse_cut (keep : Set HighAnnularMode) (data : AnnularForcing lower × AnnularBoundary) :
    annularVariationalInverse parameters lower length positive collar lengthPositive widthHalf widthLength
      (annularDataCut lower keep data) =
        annularEnergyCut lower length positive keep
          (annularVariationalInverse parameters lower length positive collar lengthPositive widthHalf widthLength data) :=
  (annularVariationalInverse_diagonal parameters lower length positive collar lengthPositive widthHalf widthLength
    (fourierMask keep) 1 (by norm_num) (fourierMask_bound keep) data).symm

/-- The actual original-width solution has every supplied split/inserted
grade, the SAME explicit base energy constant, the original inner value
and complex weak equation, and full weighted energy/trace cutoff convergence.
Literal carrier identities, complete normalized models and compatible
injective grade inclusions are proved in AAT9–16. -/
theorem annularGradedInverse_consumer (angular cell inserted : ℕ)
    (data : AnnularForcing lower × AnnularBoundary)
    (grade : HasAnnularDataGrade lower angular cell inserted data) :
    ∃ solutionGrade : HasAnnularEnergyGrade lower length positive angular cell inserted
        (annularVariationalInverse parameters lower length positive collar lengthPositive widthHalf widthLength data),
      annularEnergyTrace lower length positive collar lengthPositive 0
        (annularVariationalInverse parameters lower length positive collar lengthPositive widthHalf widthLength data) = data.2 ∧
      (∀ test : annularInnerZero lower length positive collar lengthPositive,
        annularFormValue parameters lower length positive lengthPositive widthHalf widthLength
          (annularVariationalInverse parameters lower length positive collar lengthPositive widthHalf widthLength data) test.val =
            annularFunctionalValue parameters lower length positive collar lengthPositive widthHalf widthLength data.1 test.val) ∧
      ‖annularWeightedEnergy lower length positive angular cell inserted
        (annularVariationalInverse parameters lower length positive collar lengthPositive widthHalf widthLength data) solutionGrade‖ ≤
        annularInnerLiftConstant lower length * ‖(annularWeightedData lower angular cell inserted data grade).2‖ +
          (4 / 3 : ℝ) * (annularForcingSize lower length (annularWeightedData lower angular cell inserted data grade).1 +
            4 * annularInnerLiftConstant lower length * ‖(annularWeightedData lower angular cell inserted data grade).2‖) ∧
      Tendsto (fun support : Finset HighAnnularMode =>
        annularWeightedEnergy lower length positive angular cell inserted
          (annularEnergyCut lower length positive (support : Set HighAnnularMode)
            (annularVariationalInverse parameters lower length positive collar lengthPositive widthHalf widthLength data))
          (annularEnergyCut_hasGrade lower length positive angular cell inserted (support : Set HighAnnularMode) _ solutionGrade))
        atTop (𝓝 (annularWeightedEnergy lower length positive angular cell inserted
          (annularVariationalInverse parameters lower length positive collar lengthPositive widthHalf widthLength data) solutionGrade)) ∧
      ∀ endpoint : Fin 2,
        Tendsto (fun support : Finset HighAnnularMode =>
          annularEnergyTrace lower length positive collar lengthPositive endpoint
            (annularWeightedEnergy lower length positive angular cell inserted
              (annularEnergyCut lower length positive (support : Set HighAnnularMode)
                (annularVariationalInverse parameters lower length positive collar lengthPositive widthHalf widthLength data))
              (annularEnergyCut_hasGrade lower length positive angular cell inserted (support : Set HighAnnularMode) _ solutionGrade)))
          atTop (𝓝 (annularEnergyTrace lower length positive collar lengthPositive endpoint
            (annularWeightedEnergy lower length positive angular cell inserted
              (annularVariationalInverse parameters lower length positive collar lengthPositive widthHalf widthLength data) solutionGrade))) := by
  let solutionGrade := annularInverse_hasGrade parameters lower length positive collar lengthPositive widthHalf widthLength
    angular cell inserted data grade
  refine ⟨solutionGrade, ?_, ?_, ?_, ?_, ?_⟩
  · exact annularVariationalSolution_inner parameters lower length positive collar lengthPositive widthHalf widthLength data.1 data.2
  · exact annularVariationalSolution_weak parameters lower length positive collar lengthPositive widthHalf widthLength data.1 data.2
  · exact annularInverse_weighted_bound parameters lower length positive collar lengthPositive widthHalf widthLength
      angular cell inserted data grade solutionGrade
  · exact annularWeightedEnergy_cut_tendsto lower length positive angular cell inserted _ solutionGrade
  · intro endpoint
    exact annularWeightedTrace_cut_tendsto lower length positive collar lengthPositive angular cell inserted endpoint _ solutionGrade

end Consumer

end Grad.AnnularGrades
