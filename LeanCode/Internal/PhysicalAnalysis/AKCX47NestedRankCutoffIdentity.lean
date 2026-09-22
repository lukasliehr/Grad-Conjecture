import AKCX46SameLocalizedPrincipalLeading
import AKCG4OriginalB10RankResolventConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxRecDepth 3000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.WeightedJets.ZeroExtension Grad.WeightedJets.Ordered Grad.TensorBootstrap

theorem startupSupported_mono {inside outside : Set Spatial} {field : StartupL2 3}
    (included : inside ⊆ outside) (supported : SupportedField (CellValues 3) openUnitDisk inside field) :
    SupportedField (CellValues 3) openUnitDisk outside field := by
  filter_upwards [supported] with point zero
  exact fun absent => zero (fun present => absent (included present))

theorem startupCutoff_supported_absorb (outer : Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ outer) (compact : HasCompactSupport outer)
    {inside : Set Spatial} (plateau : ∀ point ∈ inside, outer point = 1)
    (field : StartupL2 3) (supported : SupportedField (CellValues 3) openUnitDisk inside field) :
    startupCutoffL2 outer smooth compact field = field := by
  apply startupField_ae_ext
  filter_upwards [startupCutoffL2_ae outer smooth compact field,supported] with point same zero
  intro cell
  rw [same cell]
  by_cases present : point ∈ inside
  · rw [plateau point present,Complex.ofReal_one,one_smul]
  · have vanish : field point cell = 0 := congrArg (fun value : CellValues 3 => value cell) (zero present)
    rw [vanish,smul_zero]

theorem startupPlateau_support {outer : Spatial → ℝ} {inside : Set Spatial}
    (plateau : ∀ point ∈ inside, outer point = 1) : inside ⊆ tsupport outer := by
  intro point present
  apply subset_tsupport
  change outer point ≠ 0
  rw [plateau point present]
  exact one_ne_zero

theorem StartupRankOperator.localizedCoarse_extension {rank : ℕ}
    (operator : StartupRankOperator rank 3 3) (outer : Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ outer) (compact : HasCompactSupport outer)
    (field : Tensor rank (StartupL2 3)) (word : DerivativeIndex rank) :
    operator.localizedCoarse outer smooth compact (hilbertLift startupPlaneExtension field) word =
      startupPlaneExtension (startupCutoffL2 outer smooth compact (operator.orderedCoarse field word)) := by
  have restricted : hilbertLift (Index := DerivativeIndex rank) startupPlaneRestriction
      (hilbertLift startupPlaneExtension field) = field := by
    apply PiLp.ext
    intro index
    exact startupPlaneRestriction_extension (field index)
  change startupPlaneExtension (startupCutoffL2 outer smooth compact
    (operator.orderedCoarse (hilbertLift startupPlaneRestriction (hilbertLift startupPlaneExtension field)) word)) = _
  rw [restricted]

/-- The actual rank split can be localized outside its SAME closed support.
No support preservation of the rank operator is used. -/
theorem startupRankLeading_nestedCutoff {rank : ℕ} {inside : Set Spatial}
    (outer : Spatial → ℝ) (smooth : ContDiff ℝ ∞ outer) (compact : HasCompactSupport outer)
    (plateau : ∀ point ∈ inside, outer point = 1)
    (operator : StartupRankOperator rank 3 3)
    (field tensor : Tensor rank (StartupL2 3))
    (supported : ∀ word, SupportedField (CellValues 3) openUnitDisk inside (tensor word))
    (remainder : StartupFirst (startupTensorDimension 3 rank))
    (same : startupTensorFieldEquiv 3 rank tensor = operator.coarse (startupTensorFieldEquiv 3 rank field)+
      base (startupTensorDimension 3 rank) 1 openUnitDisk (fun _ => 0) remainder) :
    ∃ known : DerivativeIndex rank → StartupFirst 3,
      (∀ word, SupportedField (CellValues 3) openUnitDisk (tsupport outer)
        (base 3 1 openUnitDisk (fun _ => 0) (known word))) ∧
      ∀ word, tensor word = startupCutoffL2 outer smooth compact (operator.orderedCoarse field word)+
        base 3 1 openUnitDisk (fun _ => 0) (known word) := by
  let unpacked := (startupTensorFirstEquiv 3 rank).symm remainder
  have values : startupTensorFirstValues unpacked =
      (startupTensorFieldEquiv 3 rank).symm (base (startupTensorDimension 3 rank) 1 openUnitDisk (fun _ => 0) remainder) :=
    startupTensorFirstEquiv_symm_values 3 rank remainder
  have unflattened : tensor = operator.orderedCoarse field + startupTensorFirstValues unpacked := by
    have identity := congrArg (startupTensorFieldEquiv 3 rank).symm same
    rw [LinearIsometryEquiv.symm_apply_apply,map_add,← values] at identity
    exact identity
  refine ⟨fun word => startupCutoffSpatialGraph outer smooth compact 1 0 (unpacked word),?_,?_⟩
  · intro word
    rw [startupCutoffSpatialGraph_base]
    exact startupCutoffL2_supported outer smooth compact _ Subset.rfl _
  · intro word
    rw [startupCutoffSpatialGraph_base]
    have coordinate := congrArg (fun tuple : Tensor rank (StartupL2 3) => tuple word) unflattened
    change tensor word = operator.orderedCoarse field word + base 3 1 openUnitDisk (fun _ => 0) (unpacked word) at coordinate
    have multiplied := congrArg (startupCutoffL2 outer smooth compact) coordinate
    rw [startupCutoff_supported_absorb outer smooth compact plateau _ (supported word),map_add] at multiplied
    exact multiplied

end Grad.CartesianStartup
