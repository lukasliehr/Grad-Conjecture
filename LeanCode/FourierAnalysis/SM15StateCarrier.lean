import SM14AxisCalculus
import ReadinessLemmas

noncomputable section

namespace Grad.SmoothingFamily

open Grad.ClosedJets Grad.CartesianState Grad.ImplementationReadiness

/-- The scalar block is the project's one-coordinate complex Euclidean
representation. Its one physical coordinate has exactly the complex norm. -/
theorem scalarEuclidean_norm (value : ComplexEuclidean 1) : ‖value‖ = ‖value 0‖ := by
  rw [EuclideanSpace.norm_eq]
  simp

/-- The one common smooth triple, with the same original phase width for
axis, three-vector and scalar. No projection is postulated. -/
abbrev StateCore (parameters : PhaseParameters) :=
  AxisCore parameters.sigma0 (ComplexEuclidean 2) ×
    ACore parameters 3 × ACore parameters 1

/-- Literal completed Cartesian product: axis grade `q+1`, vector and scalar
grade `q`, and the original sum norm at both product nodes. -/
abbrev XAmbient (parameters : PhaseParameters) (grade : ℕ) :=
  StateAmbient (TGrade parameters.sigma0 (ComplexEuclidean 2) (grade + 1))
    (AGrade parameters 3 grade) (AGrade parameters 1 grade)

def stateToGrade (parameters : PhaseParameters) (grade : ℕ) :
    StateCore parameters →ₗ[ℂ] XAmbient parameters grade where
  toFun state := statePack (axisToGrade parameters.sigma0 (grade + 1) state.1)
    (aGradeEta parameters (GradeCore.ofCoreLinear state.2.1))
    (aGradeEta parameters (GradeCore.ofCoreLinear state.2.2))
  map_add' first second := by
    apply (WithLp.equiv 1 _).injective
    apply Prod.ext
    · exact (axisToGrade parameters.sigma0 (grade + 1)).map_add first.1 second.1
    · apply (WithLp.equiv 1 _).injective
      apply Prod.ext
      · change aGradeEta parameters (GradeCore.ofCoreLinear (first.2.1 + second.2.1)) =
          aGradeEta parameters (GradeCore.ofCoreLinear first.2.1) + aGradeEta parameters (GradeCore.ofCoreLinear second.2.1)
        simp only [map_add]
      · change aGradeEta parameters (GradeCore.ofCoreLinear (first.2.2 + second.2.2)) =
          aGradeEta parameters (GradeCore.ofCoreLinear first.2.2) + aGradeEta parameters (GradeCore.ofCoreLinear second.2.2)
        simp only [map_add]
  map_smul' scalar state := by
    apply (WithLp.equiv 1 _).injective
    apply Prod.ext
    · exact (axisToGrade parameters.sigma0 (grade + 1)).map_smul scalar state.1
    · apply (WithLp.equiv 1 _).injective
      apply Prod.ext
      · change aGradeEta parameters (GradeCore.ofCoreLinear (scalar • state.2.1)) =
          scalar • aGradeEta parameters (GradeCore.ofCoreLinear state.2.1)
        simp only [map_smul]
      · change aGradeEta parameters (GradeCore.ofCoreLinear (scalar • state.2.2)) =
          scalar • aGradeEta parameters (GradeCore.ofCoreLinear state.2.2)
        simp only [map_smul]

theorem stateToGrade_norm (parameters : PhaseParameters) (grade : ℕ) (state : StateCore parameters) :
    ‖stateToGrade parameters grade state‖ =
      ‖axisToGrade parameters.sigma0 (grade + 1) state.1‖ +
      ‖GradeCore.ofCoreLinear (grade := grade) state.2.1‖ +
      ‖GradeCore.ofCoreLinear (grade := grade) state.2.2‖ := by
  change ‖statePack _ _ _‖ = _
  rw [statePack_norm, aGradeEta_norm, aGradeEta_norm]

theorem stateToGrade_injective (parameters : PhaseParameters) (grade : ℕ) :
    Function.Injective (stateToGrade parameters grade) := by
  intro first second equality
  have axis := congrArg (fun value : XAmbient parameters grade => value.ofLp.1) equality
  have vector := congrArg (fun value : XAmbient parameters grade => value.ofLp.2.ofLp.1) equality
  have scalar := congrArg (fun value : XAmbient parameters grade => value.ofLp.2.ofLp.2) equality
  apply Prod.ext (axisToGrade_injective parameters.sigma0 (grade + 1) axis)
  exact Prod.ext (congrArg GradeCore.toCore (aGradeEta_injective parameters vector))
    (congrArg GradeCore.toCore (aGradeEta_injective parameters scalar))

/-- The actual smooth states with the inherited grade norm, inside the
literal sum-norm product. This is not an auxiliary Fourier norm. -/
abbrev StateGradeCore (parameters : PhaseParameters) (grade : ℕ) :=
  (stateToGrade parameters grade).range

def stateGradeEquiv (parameters : PhaseParameters) (grade : ℕ) :
    StateCore parameters ≃ₗ[ℂ] StateGradeCore parameters grade :=
  LinearEquiv.ofInjective (stateToGrade parameters grade) (stateToGrade_injective parameters grade)

theorem stateGradeEquiv_coe (parameters : PhaseParameters) (grade : ℕ) (state : StateCore parameters) :
    (stateGradeEquiv parameters grade state).1 = stateToGrade parameters grade state := rfl

theorem stateGradeEquiv_norm (parameters : PhaseParameters) (grade : ℕ) (state : StateCore parameters) :
    ‖stateGradeEquiv parameters grade state‖ = ‖stateToGrade parameters grade state‖ := rfl

end Grad.SmoothingFamily
