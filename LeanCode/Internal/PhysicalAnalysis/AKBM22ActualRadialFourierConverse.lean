import AKBM21ActualOriginalCorrectedScalar

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set Filter
open scoped Topology ContDiff
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.ActualPolarFlux Grad.ActualCartesianEquations
open Grad.SourceCollarFullSource Grad.ActualDeterminantEquations
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.AnnularSourceGraph Grad.AnnularSmoothCore Grad.BoundaryTrace

/-- Read a genuine radial derivative back into its exact Fourier slopes.
Absolute convergence is supplied by the accepted all-grade Hilbert jets. -/
theorem originalScalarRadial_doubleCoefficient {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    {row : DivisionRow 1 lower} (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower<1)
    (radius : ℝ) (inside : radius∈Ioo lower 1) (slopes : (ℤ×ℤ)→ComplexEuclidean 1)
    (derivatives : ∀ mode, HasDerivWithinAt (fun location => curves.physicalCurve 0 location mode)
      (slopes mode) (Icc lower 1) radius) (mode : ℤ×ℤ) :
    doubleCoefficient (fun angles => WithLp.toLp 2 (fun _ : Fin 1 =>
      scalarDirectionalField curves bounded 0 (1,0,0) (radius,angles))) mode=slopes mode := by
  have closed : radius∈Icc lower 1 := ⟨inside.1.le,inside.2.le⟩
  let smooth := curves.physicalCurve_smooth bounded
  have same (grade : ℕ) (location : ℝ) (member : location∈Icc lower 1) (query : ℤ×ℤ) :
      curves.physicalCurve grade location query=
        ((Grad.AnnularVariational.annularFrequency query.1 query.2^grade:ℝ):ℂ) • curves.physicalCurve 0 location query := by
    rw [curves.physicalCurve_grade bounded grade location member query,Complex.ofReal_pow]
    rfl
  have sectionSame (query : ℤ×ℤ) :
      hilbertRadialJetSection lower bounded curves.physicalCurve smooth 1 0 query ⟨radius,closed⟩=slopes query := by
    have jet := hilbertRadialJetSection_derivative lower bounded curves.physicalCurve smooth 0 0 query radius closed
    simp only [iteratedDerivWithin_zero,Nat.zero_add] at jet
    exact (jet.derivWithin (uniqueDiffOn_Icc bounded radius closed)).symm.trans
      ((derivatives query).derivWithin (uniqueDiffOn_Icc bounded radius closed))
  have sectionSummable : Summable (fun query : ℤ×ℤ => ‖hilbertRadialJetSection lower bounded curves.physicalCurve smooth 1 0 query‖) := by
    simpa only [pow_zero,one_mul] using hilbertRadialJetSection_weighted_summable lower bounded curves.physicalCurve smooth same 1 0
  have summable : Summable (fun query => ‖slopes query‖) := by
    apply Summable.of_nonneg_of_le (fun query => norm_nonneg _) (fun query => ?_) sectionSummable
    rw [← sectionSame query]
    exact (hilbertRadialJetSection lower bounded curves.physicalCurve smooth 1 0 query).norm_coe_le_norm ⟨radius,closed⟩
  have seriesCoefficient (query : ℤ×ℤ) : doubleCoefficient (physicalCharacterSeries slopes) query=slopes query := by
    rw [doubleCoefficient, doubleCoefficient_swap _ (physicalCharacterSeries_continuous slopes summable),physicalCharacterSeries_coefficient slopes summable query]
  have sameDerivative (angles : ℝ×ℝ) : physicalCharacterSeries slopes angles=
      WithLp.toLp 2 (fun _ : Fin 1 => scalarDirectionalField curves bounded 0 (1,0,0) (radius,angles)) := by
    have given := hilbertPhysicalField_radial_of_coefficients lower positive bounded curves.physicalCurve smooth same
      radius closed slopes derivatives angles
    have actual : HasDerivWithinAt (fun location => curves.fullField bounded (location,angles))
        (physicalCharacterSeries slopes angles) (Icc lower 1) radius := by
      apply given.congr
      · intro location member
        rw [fullField_scalarSeries curves bounded location member angles]
        simp only [hilbertPhysicalField,radialClamp_eq lower bounded.le location member]
      · rw [fullField_scalarSeries curves bounded radius closed angles]
        simp only [hilbertPhysicalField,radialClamp_eq lower bounded.le radius closed]
    have derivative := actual.hasDerivAt (Icc_mem_nhds inside.1 inside.2)
    have component := ((PiLp.proj (𝕜:=ℂ) 2 (fun _ : Fin 1 => ℂ) 0).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt radius derivative
    have actual := component.unique (scalarRadial_hasDerivAt curves bounded 0 radius inside angles.1 angles.2)
    apply PiLp.ext
    intro index
    fin_cases index
    exact actual
  rw [← funext sameDerivative,seriesCoefficient]

end Grad.OriginalKernelHomogeneousGraph
