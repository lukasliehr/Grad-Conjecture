import AKDE17ActualPartialDerivativePackets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
open scoped ContDiff Topology BigOperators
namespace Grad.OriginalCellFamily
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem compactSpatialDerivative_zero_bound (radius : ℝ) (positive : 0 < radius)
    (parameterLower parameterUpper lower upper : ℝ)
    (contains : parameterLower < lower ∧ upper < parameterUpper)
    (spatialDomain : Set X) (openSpatial : IsOpen spatialDomain)
    (compact : Set X) (compactSet : IsCompact compact) (included : compact ⊆ spatialDomain)
    (field : ℝ × (ℝ × X) → Y)
    (smooth : ContDiffOn ℝ ∞ field (Ioo (-radius) radius ×ˢ (Ioo parameterLower parameterUpper ×ˢ spatialDomain)))
    (zero : ∀ parameter ∈ Icc lower upper, ∀ point ∈ compact, ∀ order : ℕ,
      iteratedFDeriv ℝ order (fun spatial => field (0,(parameter,spatial))) point = 0)
    (order : ℕ) :
    ∃ constant : ℝ, 1 ≤ constant ∧ ∀ epsilon : ℝ, |epsilon| ≤ radius/2 →
      ∀ parameter ∈ Icc lower upper, ∀ point ∈ compact,
        ‖iteratedFDeriv ℝ order (fun spatial => field (epsilon,(parameter,spatial))) point‖ ≤ constant * |epsilon| := by
  let domain := (Ioo (-radius) radius ×ˢ Ioo parameterLower parameterUpper) ×ˢ spatialDomain
  let joint : (ℝ × ℝ) × X → Y := fun point => field (point.1.1,(point.1.2,point.2))
  have domainOpen : IsOpen domain := (isOpen_Ioo.prod isOpen_Ioo).prod openSpatial
  have jointSmooth : ContDiffOn ℝ ∞ joint domain :=
    smooth.comp (show ContDiffOn ℝ ∞ (fun point : (ℝ × ℝ) × X => (point.1.1,(point.1.2,point.2))) domain by fun_prop)
      (fun _ member => ⟨member.1.1,member.1.2,member.2⟩)
  let packet : ℝ × (ℝ × X) → ContinuousMultilinearMap ℝ (fun _ : Fin order => X) Y :=
    fun point => spatialDerivativePacket order joint ((point.1,point.2.1),point.2.2)
  have packetSmooth : ContDiffOn ℝ ∞ packet
      (Ioo (-radius) radius ×ˢ (Ioo parameterLower parameterUpper ×ˢ spatialDomain)) :=
    (spatialDerivativePacket_joint_smooth domain domainOpen joint jointSmooth order).comp
      (show ContDiffOn ℝ ∞ (fun point : ℝ × (ℝ × X) => ((point.1,point.2.1),point.2.2)) _ by fun_prop)
      (fun _ member => ⟨⟨member.1,member.2.1⟩,member.2.2⟩)
  have parameterInside {parameter : ℝ} (member : parameter ∈ Icc lower upper) : parameter ∈ Ioo parameterLower parameterUpper :=
    ⟨contains.1.trans_le member.1,member.2.trans_lt contains.2⟩
  have packetZero : ∀ point ∈ Icc lower upper ×ˢ compact, packet (0,point)=0 := by
    intro point member
    exact zero point.1 member.1 point.2 member.2 order
  obtain ⟨constant,large,bound⟩ := compactParameter_zero_bound radius positive
    (Ioo parameterLower parameterUpper ×ˢ spatialDomain) (isOpen_Ioo.prod openSpatial)
    (Icc lower upper ×ˢ compact) (isCompact_Icc.prod compactSet)
    (fun _ member => ⟨parameterInside member.1,included member.2⟩) packet packetSmooth packetZero
  refine ⟨constant,large,?_⟩
  intro epsilon small parameter parameterIn point pointIn
  exact bound epsilon small (parameter,point) ⟨parameterIn,pointIn⟩

/-- One uniform constant controls all actual physical derivatives through
order two, with the independent parameter held fixed in each derivative. -/
theorem compactC2_zero_bound (radius : ℝ) (positive : 0 < radius)
    (parameterLower parameterUpper lower upper : ℝ)
    (contains : parameterLower < lower ∧ upper < parameterUpper)
    (spatialDomain : Set X) (openSpatial : IsOpen spatialDomain)
    (compact : Set X) (compactSet : IsCompact compact) (included : compact ⊆ spatialDomain)
    (field : ℝ × (ℝ × X) → Y)
    (smooth : ContDiffOn ℝ ∞ field (Ioo (-radius) radius ×ˢ (Ioo parameterLower parameterUpper ×ˢ spatialDomain)))
    (zero : ∀ parameter ∈ Icc lower upper, ∀ point ∈ compact, ∀ order : ℕ,
      iteratedFDeriv ℝ order (fun spatial => field (0,(parameter,spatial))) point = 0) :
    ∃ constant : ℝ, 1 ≤ constant ∧ ∀ epsilon : ℝ, |epsilon| ≤ radius/2 →
      ∀ parameter ∈ Icc lower upper, ∀ point ∈ compact, ∀ order : Fin 3,
        ‖iteratedFDeriv ℝ order.val (fun spatial => field (epsilon,(parameter,spatial))) point‖ ≤ constant * |epsilon| := by
  have supplied (order : Fin 3) := compactSpatialDerivative_zero_bound radius positive parameterLower parameterUpper lower upper
    contains spatialDomain openSpatial compact compactSet included field smooth zero order.val
  choose constant large bound using supplied
  have nonnegative (order : Fin 3) : 0 ≤ constant order := (by norm_num : (0:ℝ)≤1).trans (large order)
  have below (order : Fin 3) : constant order ≤ ∑ index : Fin 3, constant index :=
    Finset.single_le_sum (fun index _ => nonnegative index) (Finset.mem_univ order)
  refine ⟨∑ order : Fin 3,constant order,(large 0).trans (below 0),?_⟩
  intro epsilon small parameter parameterIn point pointIn order
  exact (bound order epsilon small parameter parameterIn point pointIn).trans
    (mul_le_mul_of_nonneg_right (below order) (abs_nonneg epsilon))

end Grad.OriginalCellFamily
