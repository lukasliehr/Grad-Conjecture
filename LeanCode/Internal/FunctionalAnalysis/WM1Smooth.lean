import WM1Approximation
import MP1BridgeTranslation

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets Grad.SpatialTranslation
open Grad.WeakTesting
open scoped Topology ContDiff

namespace Grad.Mollifier.WeakJets

universe valueUniverse

theorem average_realization (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [InnerProductSpace ℂ Value] [CompleteSpace Value] (kernel : Spatial → ℝ)
    (integrability : Integrable kernel volume) (field : DomainL2 Value Set.univ) :
    average Value kernel field =ᵐ[volume] Pointwise.smoothRepresentative Value kernel field ∧
      MemLp (Pointwise.smoothRepresentative Value kernel field) 2 volume :=
  Pointwise.Bridge.translationSpecializationGoal Value kernel integrability field
    (kernel_integrand_integrable Value kernel integrability field) (fun offset => translation_ae Value offset field)

theorem weighted_kernel_identity (dimension order : ℕ) (exponent : JetIndex order → ℕ)
    (kernel : Spatial → ℝ) (smoothness : ContDiff ℝ ∞ kernel) (compactSupport : HasCompactSupport kernel)
    (jet : WJet dimension order Set.univ exponent) (index : JetIndex order) (point : Spatial) (cell : ℤ) :
    Pointwise.smoothRepresentative (CellValues dimension) kernel (jet.val index) point cell =
      Grad.CellWeights.positiveFactor (exponent index) cell •
        Pointwise.orderedDerivative (degree index) (derivativeWord index)
          (Pointwise.smoothRepresentative (CellValues dimension) kernel
            (base dimension order Set.univ exponent jet)) point cell := by
  let test : TestFunction Set.univ :=
    ⟨reflectedKernel point kernel, reflectedKernel_contDiff point kernel smoothness,
      reflectedKernel_compactSupport point kernel compactSupport, Set.subset_univ _⟩
  have baseCalculus := Pointwise.pointwiseGoal (CellValues dimension) kernel smoothness compactSupport
    (base dimension order Set.univ exponent jet)
  have coordinateCalculus :=
    Pointwise.pointwiseGoal (CellValues dimension) kernel smoothness compactSupport (jet.val index)
  apply ext_inner_left ℂ
  intro vector
  have identity := jet_identity dimension order Set.univ exponent jet index cell vector test
  simp only [testPairing_apply, derivativeTestPairing_apply, Measure.restrict_univ] at identity
  change (∫ source : Spatial, kernel (point - source) • inner ℂ vector (jet.val index source cell)) =
    ((-1 : ℂ) ^ degree index * Grad.CellWeights.positiveFactor (exponent index) cell) *
      ∫ source : Spatial, orderedTestDerivative (degree index) (derivativeWord index)
        (reflectedKernel point kernel) source • inner ℂ vector
          (base dimension order Set.univ exponent jet source cell) at identity
  simp_rw [orderedTestDerivative_reflected _ _ point kernel smoothness] at identity
  rw [mul_comm ((-1 : ℂ) ^ degree index), mul_assoc, reflected_sign_integral] at identity
  have derivativePairing := (congrArg (fun values : CellValues dimension => inner ℂ vector (values cell))
    (baseCalculus.2.2 (degree index) (derivativeWord index) point).2).trans
      (integral_cell_inner dimension (base dimension order Set.univ exponent jet) _
        (baseCalculus.2.2 (degree index) (derivativeWord index) point).1 cell vector)
  rw [inner_smul_right]
  exact (integral_cell_inner dimension (jet.val index) _ (coordinateCalculus.1 point) cell vector).trans
    (identity.trans (congrArg (fun value : ℂ => Grad.CellWeights.positiveFactor (exponent index) cell * value)
      derivativePairing.symm))

theorem inverse_positive_cancel (weight : ℕ) (cell : ℤ) :
    Grad.CellWeights.inverseFactor weight cell * Grad.CellWeights.positiveFactor weight cell = 1 := by
  apply inv_mul_cancel₀
  exact pow_ne_zero weight (Complex.ofReal_ne_zero.mpr (Grad.CellWeights.cellWeight_pos cell).ne')

theorem regularized_derivative_ae (dimension order : ℕ) (exponent : JetIndex order → ℕ)
    (epsilon : ℝ) (positive : 0 < epsilon) (jet : WJet dimension order Set.univ exponent)
    (index : JetIndex order) :
    Grad.CellWeights.inverseFieldCLM dimension Set.univ (exponent index)
        (regularizedTuple dimension order epsilon jet.val index) =ᵐ[volume]
      Pointwise.orderedDerivative (degree index) (derivativeWord index)
        (Pointwise.smoothRepresentative (CellValues dimension) (Pointwise.scaledEta epsilon)
          (base dimension order Set.univ exponent jet)) := by
  have inverseRepresentation := Grad.CellWeights.inverseFieldCLM_coordinate dimension Set.univ
    (exponent index) (regularizedTuple dimension order epsilon jet.val index)
  have inverseVolume := Grad.SpatialTranslation.ae_univ_iff.mp inverseRepresentation
  have realization := (average_realization (CellValues dimension) (Pointwise.scaledEta epsilon)
    (Pointwise.scaledEta_integrable epsilon positive) (jet.val index)).1
  filter_upwards [inverseVolume, realization] with point inverseCoordinates represented
  apply lp.ext
  funext cell
  rw [inverseCoordinates cell]
  change Grad.CellWeights.inverseFactor (exponent index) cell •
    (average (CellValues dimension) (Pointwise.scaledEta epsilon) (jet.val index) point cell) = _
  rw [represented, weighted_kernel_identity dimension order exponent _
    (Pointwise.scaledEta_contDiff epsilon) (Pointwise.scaledEta_compactSupport epsilon positive),
    smul_smul, inverse_positive_cancel, one_smul]

theorem smoothGoal : SmoothGoal := by
  intro dimension order exponent epsilon positive jet
  have kernelSmooth := Pointwise.scaledEta_contDiff epsilon
  have kernelCompact := Pointwise.scaledEta_compactSupport epsilon positive
  refine ⟨(Pointwise.pointwiseGoal (CellValues dimension) _ kernelSmooth kernelCompact
    (base dimension order Set.univ exponent jet)).2.1, ?_⟩
  intro index
  have represented := regularized_derivative_ae dimension order exponent epsilon positive jet index
  have membership : MemLp (Grad.CellWeights.inverseFieldCLM dimension Set.univ (exponent index)
      (regularizedTuple dimension order epsilon jet.val index)) 2 volume := by
    simpa only [Measure.restrict_univ] using Lp.memLp
      (Grad.CellWeights.inverseFieldCLM dimension Set.univ (exponent index)
        (regularizedTuple dimension order epsilon jet.val index))
  exact ⟨(Pointwise.pointwiseGoal (CellValues dimension) _ kernelSmooth kernelCompact (jet.val index)).2.1,
    (average_realization (CellValues dimension) _ (Pointwise.scaledEta_integrable epsilon positive) (jet.val index)).1,
    represented, MemLp.ae_eq represented membership,
    weighted_kernel_identity dimension order exponent _ kernelSmooth kernelCompact jet index⟩

end Grad.Mollifier.WeakJets
