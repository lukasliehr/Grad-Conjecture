import WM1Translation

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open Grad.WeakTesting.Commutation (HasWeakOrderedDerivative)
open scoped ContDiff

namespace Grad.Mollifier.WeakJets

theorem independentGoal : IndependentGoal := ⟨testGoal, kernelWeakGoal, translationWeakGoal⟩

namespace Consumer

theorem independentBlock : IndependentGoal := independentGoal

theorem kernelOrderedValue (dimension rank : ℕ) (word : Fin rank → Fin 2)
    (field derivative : FieldL2 dimension Set.univ)
    (weakDerivative : HasWeakOrderedDerivative dimension Set.univ rank word field derivative)
    (kernel : Spatial → ℝ) (smoothness : ContDiff ℝ ∞ kernel)
    (compactSupport : HasCompactSupport kernel) (point : Spatial) :
    iteratedFDeriv ℝ rank
        (Pointwise.smoothRepresentative (CellValues dimension) kernel field) point
        (fun position => spatialDirection (word position)) =
      ∫ source : Spatial, kernel (point - source) • derivative source :=
  congrFun (kernelWeakGoal dimension rank word field derivative weakDerivative kernel smoothness compactSupport) point

theorem kernelIntegralIdentity (dimension rank : ℕ) (word : Fin rank → Fin 2)
    (field derivative : FieldL2 dimension Set.univ)
    (weakDerivative : HasWeakOrderedDerivative dimension Set.univ rank word field derivative)
    (kernel : Spatial → ℝ) (smoothness : ContDiff ℝ ∞ kernel)
    (compactSupport : HasCompactSupport kernel) (point : Spatial) :
    Integrable (fun source : Spatial =>
      Pointwise.orderedDerivative rank word kernel (point - source) • field source) volume ∧
    Integrable (fun source : Spatial => kernel (point - source) • derivative source) volume ∧
    (∫ source : Spatial, Pointwise.orderedDerivative rank word kernel (point - source) • field source) =
      ∫ source : Spatial, kernel (point - source) • derivative source := by
  have fieldCalculus := Pointwise.pointwiseGoal (CellValues dimension) kernel smoothness compactSupport field
  have derivativeCalculus :=
    Pointwise.pointwiseGoal (CellValues dimension) kernel smoothness compactSupport derivative
  exact ⟨(fieldCalculus.2.2 rank word point).1, derivativeCalculus.1 point,
    (fieldCalculus.2.2 rank word point).2.symm.trans
      (kernelOrderedValue dimension rank word field derivative weakDerivative kernel smoothness compactSupport point)⟩

theorem translatedWeakFamily (dimension rank : ℕ) (field : FieldL2 dimension Set.univ)
    (derivatives : OrderedFields dimension rank Set.univ)
    (weakFamily : ∀ word : Fin rank → Fin 2,
      HasWeakOrderedDerivative dimension Set.univ rank word field (derivatives word))
    (offset : Spatial) (word : Fin rank → Fin 2) :
    HasWeakOrderedDerivative dimension Set.univ rank word
      (Grad.SpatialTranslation.translation (CellValues dimension) offset field)
      (Grad.SpatialTranslation.translation (CellValues dimension) offset (derivatives word)) :=
  translationWeakGoal dimension rank word field (derivatives word) (weakFamily word) offset

theorem zeroRank (dimension : ℕ) (word : Fin 0 → Fin 2)
    (field derivative : FieldL2 dimension Set.univ)
    (weakDerivative : HasWeakOrderedDerivative dimension Set.univ 0 word field derivative)
    (kernel : Spatial → ℝ) (smoothness : ContDiff ℝ ∞ kernel)
    (compactSupport : HasCompactSupport kernel) :
    Pointwise.smoothRepresentative (CellValues dimension) kernel field =
      Pointwise.smoothRepresentative (CellValues dimension) kernel derivative := by
  have equality := kernelWeakGoal dimension 0 word field derivative weakDerivative kernel smoothness compactSupport
  rw [Pointwise.orderedDerivative_zero] at equality
  exact equality

theorem zeroDimension (rank : ℕ) (word : Fin rank → Fin 2)
    (field derivative : FieldL2 0 Set.univ)
    (weakDerivative : HasWeakOrderedDerivative 0 Set.univ rank word field derivative)
    (kernel : Spatial → ℝ) (smoothness : ContDiff ℝ ∞ kernel)
    (compactSupport : HasCompactSupport kernel) :
    Pointwise.orderedDerivative rank word (Pointwise.smoothRepresentative (CellValues 0) kernel field) =
      Pointwise.smoothRepresentative (CellValues 0) kernel derivative :=
  kernelWeakGoal 0 rank word field derivative weakDerivative kernel smoothness compactSupport

end Consumer

end Grad.Mollifier.WeakJets
