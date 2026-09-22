import SM7Ambient

noncomputable section

open scoped Topology

namespace Grad.SmoothingFamily

open Grad.ClosedJets Grad.CartesianState

/-- Pull a genuine derivative back through the literal isometric completion
embedding; the derivative is in the original normed grade core itself. -/
theorem hasDerivAt_of_eta {dimension grade : ℕ} (parameters : PhaseParameters)
    (curve : ℝ → GradeCore parameters dimension grade) (derivative : GradeCore parameters dimension grade)
    (scale : ℝ) (checked : HasDerivAt (fun parameter => aGradeEta parameters (curve parameter))
      (aGradeEta parameters derivative) scale) : HasDerivAt curve derivative scale := by
  let etaMap := (aGradeEta (dimension := dimension) (grade := grade) parameters).restrictScalars ℝ
  have etaNorm : ∀ value, ‖etaMap value‖ = ‖value‖ := fun value => aGradeEta_norm parameters value
  change HasDerivAt (fun parameter => etaMap (curve parameter)) (etaMap derivative) scale at checked
  rw [hasDerivAt_iff_tendsto] at checked ⊢
  simpa only [← map_smul etaMap, ← map_sub etaMap, etaNorm] using checked

theorem ambientScaleDerivative_hasDerivAt_grade {dimension : ℕ} (parameters : PhaseParameters)
    (order grade : ℕ) (scale : ℝ) (positive : 0 < scale) (field : ACore parameters dimension) :
    HasDerivAt (fun parameter => GradeCore.ofCoreLinear (grade := grade)
      (ambientScaleDerivative parameters order parameter field))
      (GradeCore.ofCoreLinear (grade := grade)
        (ambientScaleDerivative parameters (order + 1) scale field)) scale :=
  hasDerivAt_of_eta parameters _ _ scale (ambientScaleDerivative_hasDerivAt parameters order grade scale positive field)

theorem iteratedDeriv_ambientSmoothing_grade {dimension : ℕ} (parameters : PhaseParameters)
    (order grade : ℕ) (scale : ℝ) (positive : 0 < scale) (field : ACore parameters dimension) :
    iteratedDeriv order (fun parameter => GradeCore.ofCoreLinear (grade := grade)
      (ambientSmoothing parameters parameter field)) scale =
      GradeCore.ofCoreLinear (grade := grade) (ambientScaleDerivative parameters order scale field) := by
  induction order generalizing scale with
  | zero => simp only [iteratedDeriv_zero, ambientScaleDerivative_zero]
  | succ order inductionHypothesis =>
    rw [iteratedDeriv_succ]
    have locallyEqual : iteratedDeriv order (fun parameter => GradeCore.ofCoreLinear (grade := grade)
        (ambientSmoothing parameters parameter field)) =ᶠ[nhds scale]
        fun parameter => GradeCore.ofCoreLinear (grade := grade)
          (ambientScaleDerivative parameters order parameter field) := by
      filter_upwards [isOpen_Ioi.mem_nhds positive] with parameter parameterPositive
      exact inductionHypothesis parameter parameterPositive
    rw [locallyEqual.deriv_eq]
    exact (ambientScaleDerivative_hasDerivAt_grade parameters order grade scale positive field).deriv

end Grad.SmoothingFamily
