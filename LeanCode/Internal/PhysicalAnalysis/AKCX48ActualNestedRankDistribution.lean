import AKCX47NestedRankCutoffIdentity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 3000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.WeightedJets.ZeroExtension Grad.WeightedJets.Ordered Grad.TensorBootstrap

/-- The literal compact differentiated ER equation supplies the whole-plane
equation required by the SAME coupled rank resolvent. -/
theorem startupSame_nestedRank_distribution {rank : ℕ} {inside : Set Spatial}
    (data : StartupCompactSpatialEquation rank inside) (closed : IsClosed inside)
    (outer : Spatial → ℝ) (smooth : ContDiff ℝ ∞ outer) (compact : HasCompactSupport outer)
    (plateau : ∀ point ∈ inside, outer point = 1)
    (localizer : TestLocalizer openUnitDisk (tsupport outer))
    (operators : Fin 2 → Fin 2 → StartupRankOperator rank 3 3)
    (leading : ∀ one two, ∃ remainder : StartupFirst (startupTensorDimension 3 rank),
      startupTensorFieldEquiv 3 rank (orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl (data.tensor one two)) =
        (operators one two).coarse (startupTensorFieldEquiv 3 rank
          (orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl data.field))+
          base (startupTensorDimension 3 rank) 1 openUnitDisk (fun _ => 0) remainder) :
    ∃ zeroth : StartupOrderedL2 rank, ∃ flux : Fin 2 → StartupOrderedL2 rank,
      ∀ word : DerivativeIndex rank,
        Laplacian.laplacian (distributionEmbedding (hilbertLift startupPlaneExtension
          (orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl data.field) word)) =
          (∑ index : TensorIndex, distributionDerivative index.1 (distributionDerivative index.2
            (distributionEmbedding ((operators index.1 index.2).localizedCoarse outer smooth compact
              (hilbertLift startupPlaneExtension (orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl data.field)) word))))+
            distributionEmbedding (zeroth word)+
            ∑ direction : Fin 2, distributionDerivative direction (distributionEmbedding (flux direction word)) := by
  let fields := orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl data.field
  let zeros := orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl data.zeroth
  let tensors := fun one two => orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl (data.tensor one two)
  let fluxes := fun direction => orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl (data.flux direction)
  have split (one two : Fin 2) : ∃ known : DerivativeIndex rank → StartupFirst 3,
      (∀ word, SupportedField (CellValues 3) openUnitDisk (tsupport outer) (base 3 1 openUnitDisk (fun _ => 0) (known word))) ∧
      ∀ word, tensors one two word = startupCutoffL2 outer smooth compact ((operators one two).orderedCoarse fields word)+
        base 3 1 openUnitDisk (fun _ => 0) (known word) := by
    obtain ⟨remainder,same⟩ := leading one two
    exact startupRankLeading_nestedCutoff outer smooth compact plateau (operators one two) fields (tensors one two)
      (fun word => startupOrderedDerivative_supported closed _ (data.tensorSupported one two) le_rfl word) remainder same
  choose known knownSupported knownSame using split
  let retained := fun one two word => startupCutoffL2 outer smooth compact ((operators one two).orderedCoarse fields word)
  let absorbed := fun direction word => fluxes direction word-
    ∑ one : Fin 2, startupFirstDerivative (known one direction word) one
  have weak (word : DerivativeIndex rank) : StartupWeakDivDivEquation (fields word) (zeros word)
      (fun one two => retained one two word) (fun direction => absorbed direction word) := by
    apply startupKnownFirstTensor_absorb
    convert data.differentiated_weak le_rfl word using 1
    funext one two
    exact (knownSame one two word).symm
  have included : inside ⊆ tsupport outer := startupPlateau_support plateau
  have fluxSupported (direction : Fin 2) (word : DerivativeIndex rank) :
      SupportedField (CellValues 3) openUnitDisk (tsupport outer) (absorbed direction word) := by
    apply startupSupported_sub
    · exact startupSupported_mono included (startupOrderedDerivative_supported closed _ (data.fluxSupported direction) le_rfl word)
    · apply startupSupported_sumTwo
      intro one
      exact startupOrderedDerivative_supported (isClosed_tsupport outer) _ (knownSupported one direction word) le_rfl (startupFirstWord one)
  refine ⟨hilbertLift startupPlaneExtension zeros,
    fun direction => -hilbertLift startupPlaneExtension (WithLp.toLp 2 (absorbed direction)),?_⟩
  intro word
  have identity := startupCompact_divDiv_distribution localizer (fields word) (zeros word)
    (fun one two => retained one two word) (fun direction => absorbed direction word)
    (startupSupported_mono included (startupOrderedDerivative_supported closed _ data.fieldSupported le_rfl word))
    (startupSupported_mono included (startupOrderedDerivative_supported closed _ data.zeroSupported le_rfl word))
    (fun one two => startupCutoffL2_supported outer smooth compact _ Subset.rfl _)
    (fun direction => fluxSupported direction word) (weak word)
  simp only [StartupRankOperator.localizedCoarse_extension]
  change Laplacian.laplacian (distributionEmbedding (startupPlaneExtension (fields word))) =
    (∑ index : TensorIndex, distributionDerivative index.1 (distributionDerivative index.2
      (distributionEmbedding (startupPlaneExtension (retained index.1 index.2 word)))))+
      distributionEmbedding (startupPlaneExtension (zeros word))+
      ∑ direction : Fin 2, distributionDerivative direction (distributionEmbedding (-startupPlaneExtension (absorbed direction word)))
  rw [Fintype.sum_prod_type]
  simp only [map_neg,Finset.sum_neg_distrib,← sub_eq_add_neg]
  exact identity

end Grad.CartesianStartup
