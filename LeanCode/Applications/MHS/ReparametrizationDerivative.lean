import ReparametrizationComposition
import ReparametrizationRegularity
import CylinderJets
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Tactic.FinCases

noncomputable section

open Set
open scoped ContDiff Topology

namespace Grad.MainAssembly.TargetReparametrization

open Grad.MainTarget
open Grad.MainTarget.SemanticBridges

local instance : Fact (0 < 2 * Real.pi) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

def coordinateCLM (coordinate : Fin 3) : Vec →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 3 => ℝ) coordinate

@[simp] theorem coordinateCLM_apply (coordinate : Fin 3) (point : Vec) :
    coordinateCLM coordinate point = point coordinate := rfl

def angleTranslate (amount : ℝ) (point : Vec) : Vec :=
  point + vector 0 0 amount

@[simp] theorem angleTranslate_apply (amount : ℝ) (point : Vec) (coordinate : Fin 3) :
    angleTranslate amount point coordinate = point coordinate + ![0, 0, amount] coordinate :=
  rfl

@[simp] theorem planarPart_angleTranslate (amount : ℝ) (point : Vec) :
    planarPart (angleTranslate amount point) = planarPart point := by
  ext coordinate
  fin_cases coordinate <;> simp [angleTranslate, planarPart, vector]

@[simp] theorem angleTranslate_mem_cylinder (amount : ℝ) (point : Vec) :
    angleTranslate amount point ∈ cylinder ↔ point ∈ cylinder := by
  simp only [cylinder, Set.mem_ofPred_eq, planarPart_angleTranslate]

theorem quotientPoint_angleTranslate (amount : ℝ) (point : Vec)
    (pointInCylinder : point ∈ cylinder)
    (amountVanishing : (amount : CellCircle) = 0) :
    quotientPoint (angleTranslate amount point)
        (angleTranslate_mem_cylinder amount point |>.mpr pointInCylinder) =
      quotientPoint point pointInCylinder := by
  apply Prod.ext
  · apply Subtype.ext
    exact planarPart_angleTranslate amount point
  · change ((point 2 + amount : ℝ) : CellCircle) = (point 2 : CellCircle)
    rw [AddCircle.coe_add, amountVanishing, add_zero]

theorem planarPart_eq_of_quotientPoint_eq {first second : Vec}
    {firstInCylinder : first ∈ cylinder} {secondInCylinder : second ∈ cylinder}
    (equality : quotientPoint first firstInCylinder = quotientPoint second secondInCylinder) :
    planarPart first = planarPart second := by
  exact congrArg (fun point : Reference => point.1.val) equality

theorem third_coe_eq_of_quotientPoint_eq {first second : Vec}
    {firstInCylinder : first ∈ cylinder} {secondInCylinder : second ∈ cylinder}
    (equality : quotientPoint first firstInCylinder = quotientPoint second secondInCylinder) :
    (first 2 : CellCircle) = (second 2 : CellCircle) := by
  exact congrArg (fun point : Reference => point.2) equality

theorem vec_eq_of_planarPart_eq_of_third_eq {first second : Vec}
    (planarEquality : planarPart first = planarPart second)
    (thirdEquality : first 2 = second 2) : first = second := by
  ext coordinate
  fin_cases coordinate
  · exact congrArg (fun point : Plane => point 0) planarEquality
  · exact congrArg (fun point : Plane => point 1) planarEquality
  · exact thirdEquality

/-- Two continuous ambient representatives of the same quotient-valued map,
which agree at the base point, agree on a smaller open neighborhood inside
the closed cylinder.  The proof uses one injective real chart of the literal
`2π` additive circle. -/
theorem locally_eq_of_quotientPoint_eq
    {first second : Vec → Vec} {base : Vec} {neighborhood : Set Vec}
    (neighborhoodOpen : IsOpen neighborhood) (baseInNeighborhood : base ∈ neighborhood)
    (firstContinuous : ContinuousAt first base) (secondContinuous : ContinuousAt second base)
    (baseEquality : first base = second base)
    (firstMaps : ∀ point ∈ neighborhood, point ∈ cylinder → first point ∈ cylinder)
    (secondMaps : ∀ point ∈ neighborhood, point ∈ cylinder → second point ∈ cylinder)
    (quotientEquality : ∀ point (pointInNeighborhood : point ∈ neighborhood)
      (pointInCylinder : point ∈ cylinder),
      quotientPoint (first point) (firstMaps point pointInNeighborhood pointInCylinder) =
        quotientPoint (second point) (secondMaps point pointInNeighborhood pointInCylinder)) :
    ∃ localNeighborhood : Set Vec,
      IsOpen localNeighborhood ∧ base ∈ localNeighborhood ∧
      localNeighborhood ⊆ neighborhood ∧
      EqOn first second (localNeighborhood ∩ cylinder) := by
  let center := second base 2
  let firstAngle := fun point : Vec => first point 2
  let secondAngle := fun point : Vec => second point 2
  have firstAngleContinuous : ContinuousAt firstAngle base :=
    (coordinateCLM 2).continuous.continuousAt.comp firstContinuous
  have secondAngleContinuous : ContinuousAt secondAngle base :=
    (coordinateCLM 2).continuous.continuousAt.comp secondContinuous
  have centerInside : center ∈ Set.Ioo (center - Real.pi) (center + Real.pi) := by
    exact ⟨sub_lt_self _ Real.pi_pos, lt_add_of_pos_right _ Real.pi_pos⟩
  have firstBaseInside : firstAngle base ∈ Set.Ioo (center - Real.pi) (center + Real.pi) := by
    rw [show firstAngle base = center by simp only [firstAngle, center, baseEquality]]
    exact centerInside
  have firstPreimageMem :
      firstAngle ⁻¹' Set.Ioo (center - Real.pi) (center + Real.pi) ∈ nhds base :=
    firstAngleContinuous.preimage_mem_nhds (isOpen_Ioo.mem_nhds firstBaseInside)
  have secondPreimageMem :
      secondAngle ⁻¹' Set.Ioo (center - Real.pi) (center + Real.pi) ∈ nhds base :=
    secondAngleContinuous.preimage_mem_nhds (isOpen_Ioo.mem_nhds centerInside)
  let localNeighborhood := interior
    (neighborhood ∩ firstAngle ⁻¹' Set.Ioo (center - Real.pi) (center + Real.pi) ∩
      secondAngle ⁻¹' Set.Ioo (center - Real.pi) (center + Real.pi))
  have baseInLocal : base ∈ localNeighborhood := by
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.inter_mem
      (Filter.inter_mem (neighborhoodOpen.mem_nhds baseInNeighborhood) firstPreimageMem)
      secondPreimageMem
  refine ⟨localNeighborhood, isOpen_interior, baseInLocal, ?_, ?_⟩
  · intro point pointInLocal
    exact (interior_subset pointInLocal).1.1
  · intro point pointMembership
    rcases pointMembership with ⟨pointInLocal, pointInCylinder⟩
    have pointInIntersection := interior_subset pointInLocal
    have pointInNeighborhood : point ∈ neighborhood := pointInIntersection.1.1
    have firstInside : firstAngle point ∈
        Set.Ioo (center - Real.pi) (center + Real.pi) := pointInIntersection.1.2
    have secondInside : secondAngle point ∈
        Set.Ioo (center - Real.pi) (center + Real.pi) := pointInIntersection.2
    have firstIco : first point 2 ∈
        Set.Ico (center - Real.pi) ((center - Real.pi) + 2 * Real.pi) := by
      change firstAngle point ∈ _
      constructor
      · exact firstInside.1.le
      · convert firstInside.2 using 1
        ring
    have secondIco : second point 2 ∈
        Set.Ico (center - Real.pi) ((center - Real.pi) + 2 * Real.pi) := by
      change secondAngle point ∈ _
      constructor
      · exact secondInside.1.le
      · convert secondInside.2 using 1
        ring
    have quotientAtPoint := quotientEquality point pointInNeighborhood pointInCylinder
    have planarEquality := planarPart_eq_of_quotientPoint_eq quotientAtPoint
    have circleEquality := third_coe_eq_of_quotientPoint_eq quotientAtPoint
    have thirdEquality : first point 2 = second point 2 :=
      (AddCircle.coe_eq_coe_iff_of_mem_Ico firstIco secondIco).mp circleEquality
    exact vec_eq_of_planarPart_eq_of_third_eq planarEquality thirdEquality

theorem regularity_order_ne_zero_of_admissible {regularity : Regularity}
    (admissible : regularity.admissible) : regularity.order ≠ 0 := by
  cases regularity with
  | finite order =>
      simp only [Regularity.admissible, Regularity.order] at admissible ⊢
      apply ne_of_gt
      exact_mod_cast (show 0 < order by omega)
  | smooth => simp [Regularity.order]

/-- For any chosen forward local lift of a target reparametrization, a
period-normalized inverse local lift has the two ambient derivative inverse
laws at the actual closed-cylinder base point. -/
theorem localLift_fderiv_has_two_sided_inverse
    (regularity : Regularity) (admissible : regularity.admissible)
    (reparametrization : Reference ≃ Reference)
    (isReparametrization : IsReparametrization regularity reparametrization)
    (point : Vec) (pointInCylinder : point ∈ cylinder)
    (forwardNeighborhood : Set Vec) (forwardOpen : IsOpen forwardNeighborhood)
    (pointInForward : point ∈ forwardNeighborhood) (forwardLift : Vec → Vec)
    (forwardSmooth : ContDiffOn ℝ regularity.order forwardLift forwardNeighborhood)
    (forwardAgreement : ∀ argument ∈ forwardNeighborhood,
      ∀ membership : argument ∈ cylinder,
        ∃ imageMembership : forwardLift argument ∈ cylinder,
          quotientPoint (forwardLift argument) imageMembership =
            reparametrization (quotientPoint argument membership)) :
    ∃ normalizedInverse : Vec → Vec,
      DifferentiableAt ℝ normalizedInverse (forwardLift point) ∧
      (fderiv ℝ normalizedInverse (forwardLift point)).comp
          (fderiv ℝ forwardLift point) = ContinuousLinearMap.id ℝ Vec ∧
      (fderiv ℝ forwardLift point).comp
          (fderiv ℝ normalizedInverse (forwardLift point)) =
        ContinuousLinearMap.id ℝ Vec := by
  obtain ⟨forwardImageInCylinder, forwardAtPoint⟩ :=
    forwardAgreement point pointInForward pointInCylinder
  rcases isReparametrization.2 (forwardLift point) forwardImageInCylinder with
    ⟨inverseNeighborhood, inverseOpen, imageInInverse,
      inverseLift, inverseSmooth, inverseAgreement⟩
  obtain ⟨inverseImageInCylinder, inverseAtImage⟩ :=
    inverseAgreement (forwardLift point) imageInInverse forwardImageInCylinder
  have inverseQuotientAtBase :
      quotientPoint (inverseLift (forwardLift point)) inverseImageInCylinder =
        quotientPoint point pointInCylinder := by
    calc
      quotientPoint (inverseLift (forwardLift point)) inverseImageInCylinder =
          reparametrization.symm
            (quotientPoint (forwardLift point) forwardImageInCylinder) := inverseAtImage
      _ = reparametrization.symm
          (reparametrization (quotientPoint point pointInCylinder)) := by rw [forwardAtPoint]
      _ = quotientPoint point pointInCylinder := reparametrization.symm_apply_apply _
  let amount := point 2 - inverseLift (forwardLift point) 2
  have amountVanishing : (amount : CellCircle) = 0 := by
    have circleEquality := third_coe_eq_of_quotientPoint_eq inverseQuotientAtBase
    change ((point 2 - inverseLift (forwardLift point) 2 : ℝ) : CellCircle) = 0
    rw [AddCircle.coe_sub, circleEquality, sub_self]
  let normalizedInverse := fun argument => angleTranslate amount (inverseLift argument)
  have normalizedSmooth :
      ContDiffOn ℝ regularity.order normalizedInverse inverseNeighborhood := by
    simpa only [normalizedInverse, angleTranslate] using
      inverseSmooth.add contDiffOn_const
  have normalizedAtBase : normalizedInverse (forwardLift point) = point := by
    apply vec_eq_of_planarPart_eq_of_third_eq
    · calc
        planarPart (normalizedInverse (forwardLift point)) =
            planarPart (inverseLift (forwardLift point)) :=
          planarPart_angleTranslate amount _
        _ = planarPart point := planarPart_eq_of_quotientPoint_eq inverseQuotientAtBase
    · change inverseLift (forwardLift point) 2 + amount = point 2
      simp only [amount]
      ring
  have normalizedMaps (argument : Vec) (argumentInInverse : argument ∈ inverseNeighborhood)
      (argumentInCylinder : argument ∈ cylinder) : normalizedInverse argument ∈ cylinder := by
    obtain ⟨inverseImageMembership, _⟩ :=
      inverseAgreement argument argumentInInverse argumentInCylinder
    exact (angleTranslate_mem_cylinder amount (inverseLift argument)).mpr
      inverseImageMembership
  have normalizedAgreement (argument : Vec)
      (argumentInInverse : argument ∈ inverseNeighborhood)
      (argumentInCylinder : argument ∈ cylinder) :
      quotientPoint (normalizedInverse argument)
          (normalizedMaps argument argumentInInverse argumentInCylinder) =
        reparametrization.symm (quotientPoint argument argumentInCylinder) := by
    obtain ⟨inverseImageMembership, inverseAtArgument⟩ :=
      inverseAgreement argument argumentInInverse argumentInCylinder
    calc
      quotientPoint (normalizedInverse argument)
          (normalizedMaps argument argumentInInverse argumentInCylinder) =
          quotientPoint (inverseLift argument) inverseImageMembership := by
        exact quotientPoint_angleTranslate amount (inverseLift argument)
          inverseImageMembership amountVanishing
      _ = reparametrization.symm (quotientPoint argument argumentInCylinder) :=
        inverseAtArgument

  have orderNonzero := regularity_order_ne_zero_of_admissible admissible
  have forwardContinuousAt : ContinuousAt forwardLift point :=
    (forwardSmooth point pointInForward).contDiffAt
      (forwardOpen.mem_nhds pointInForward) |>.continuousAt
  have forwardDifferentiableAt : DifferentiableAt ℝ forwardLift point :=
    (forwardSmooth point pointInForward).contDiffAt
      (forwardOpen.mem_nhds pointInForward) |>.differentiableAt orderNonzero
  have normalizedContinuousAt : ContinuousAt normalizedInverse (forwardLift point) :=
    (normalizedSmooth (forwardLift point) imageInInverse).contDiffAt
      (inverseOpen.mem_nhds imageInInverse) |>.continuousAt
  have normalizedDifferentiableAt : DifferentiableAt ℝ normalizedInverse (forwardLift point) :=
    (normalizedSmooth (forwardLift point) imageInInverse).contDiffAt
      (inverseOpen.mem_nhds imageInInverse) |>.differentiableAt orderNonzero

  let firstCompositionNeighborhood :=
    interior (forwardNeighborhood ∩ forwardLift ⁻¹' inverseNeighborhood)
  have pointInFirstComposition : point ∈ firstCompositionNeighborhood := by
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.inter_mem (forwardOpen.mem_nhds pointInForward)
      (forwardContinuousAt.preimage_mem_nhds (inverseOpen.mem_nhds imageInInverse))
  have firstCompositionSmooth : ContDiffOn ℝ regularity.order
      (normalizedInverse ∘ forwardLift) firstCompositionNeighborhood := by
    exact (normalizedSmooth.comp_inter forwardSmooth).mono interior_subset
  have firstCompositionMaps (argument : Vec)
      (argumentInComposition : argument ∈ firstCompositionNeighborhood)
      (argumentInCylinder : argument ∈ cylinder) :
      (normalizedInverse ∘ forwardLift) argument ∈ cylinder := by
    have argumentInIntersection := interior_subset argumentInComposition
    obtain ⟨forwardImageMembership, _⟩ :=
      forwardAgreement argument argumentInIntersection.1 argumentInCylinder
    exact normalizedMaps (forwardLift argument) argumentInIntersection.2
      forwardImageMembership
  have firstCompositionQuotient (argument : Vec)
      (argumentInComposition : argument ∈ firstCompositionNeighborhood)
      (argumentInCylinder : argument ∈ cylinder) :
      quotientPoint ((normalizedInverse ∘ forwardLift) argument)
          (firstCompositionMaps argument argumentInComposition argumentInCylinder) =
        quotientPoint argument argumentInCylinder := by
    have argumentInIntersection := interior_subset argumentInComposition
    obtain ⟨forwardImageMembership, forwardAtArgument⟩ :=
      forwardAgreement argument argumentInIntersection.1 argumentInCylinder
    calc
      quotientPoint ((normalizedInverse ∘ forwardLift) argument)
          (firstCompositionMaps argument argumentInComposition argumentInCylinder) =
          reparametrization.symm
            (quotientPoint (forwardLift argument) forwardImageMembership) := by
        exact normalizedAgreement (forwardLift argument) argumentInIntersection.2
          forwardImageMembership
      _ = reparametrization.symm
          (reparametrization (quotientPoint argument argumentInCylinder)) := by
        rw [forwardAtArgument]
      _ = quotientPoint argument argumentInCylinder := reparametrization.symm_apply_apply _
  obtain ⟨firstExactNeighborhood, firstExactOpen, pointInFirstExact,
      firstExactSubset, firstExactAgreement⟩ :=
    locally_eq_of_quotientPoint_eq isOpen_interior pointInFirstComposition
      (normalizedContinuousAt.comp forwardContinuousAt) continuousAt_id normalizedAtBase
      firstCompositionMaps (fun argument _ membership => membership)
      firstCompositionQuotient
  have firstExactSmooth : ContDiffOn ℝ regularity.order
      (normalizedInverse ∘ forwardLift) firstExactNeighborhood :=
    firstCompositionSmooth.mono firstExactSubset
  have firstWithinDerivative :
      fderivWithin ℝ id cylinder point =
        fderiv ℝ (normalizedInverse ∘ forwardLift) point :=
    localExtension_fderivWithin uniqueDiffOn_cylinder pointInCylinder firstExactOpen
      pointInFirstExact firstExactSmooth firstExactAgreement orderNonzero
  have firstDerivativeInverse :
      (fderiv ℝ normalizedInverse (forwardLift point)).comp
          (fderiv ℝ forwardLift point) = ContinuousLinearMap.id ℝ Vec := by
    calc
      (fderiv ℝ normalizedInverse (forwardLift point)).comp
          (fderiv ℝ forwardLift point) =
          fderiv ℝ (normalizedInverse ∘ forwardLift) point :=
        (fderiv_comp point normalizedDifferentiableAt forwardDifferentiableAt).symm
      _ = fderivWithin ℝ id cylinder point := firstWithinDerivative.symm
      _ = ContinuousLinearMap.id ℝ Vec :=
        fderivWithin_id (uniqueDiffOn_cylinder point pointInCylinder)

  let secondCompositionNeighborhood :=
    interior (inverseNeighborhood ∩ normalizedInverse ⁻¹' forwardNeighborhood)
  have imageInSecondComposition : forwardLift point ∈ secondCompositionNeighborhood := by
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.inter_mem (inverseOpen.mem_nhds imageInInverse)
      (normalizedContinuousAt.preimage_mem_nhds (by
        rw [normalizedAtBase]
        exact forwardOpen.mem_nhds pointInForward))
  have secondCompositionSmooth : ContDiffOn ℝ regularity.order
      (forwardLift ∘ normalizedInverse) secondCompositionNeighborhood := by
    exact (forwardSmooth.comp_inter normalizedSmooth).mono interior_subset
  have secondCompositionMaps (argument : Vec)
      (argumentInComposition : argument ∈ secondCompositionNeighborhood)
      (argumentInCylinder : argument ∈ cylinder) :
      (forwardLift ∘ normalizedInverse) argument ∈ cylinder := by
    have argumentInIntersection := interior_subset argumentInComposition
    have normalizedImageMembership :=
      normalizedMaps argument argumentInIntersection.1 argumentInCylinder
    obtain ⟨forwardImageMembership, _⟩ :=
      forwardAgreement (normalizedInverse argument) argumentInIntersection.2
        normalizedImageMembership
    exact forwardImageMembership
  have secondCompositionQuotient (argument : Vec)
      (argumentInComposition : argument ∈ secondCompositionNeighborhood)
      (argumentInCylinder : argument ∈ cylinder) :
      quotientPoint ((forwardLift ∘ normalizedInverse) argument)
          (secondCompositionMaps argument argumentInComposition argumentInCylinder) =
        quotientPoint argument argumentInCylinder := by
    have argumentInIntersection := interior_subset argumentInComposition
    have normalizedImageMembership :=
      normalizedMaps argument argumentInIntersection.1 argumentInCylinder
    have normalizedAtArgument :=
      normalizedAgreement argument argumentInIntersection.1 argumentInCylinder
    obtain ⟨forwardImageMembership, forwardAtArgument⟩ :=
      forwardAgreement (normalizedInverse argument) argumentInIntersection.2
        normalizedImageMembership
    calc
      quotientPoint ((forwardLift ∘ normalizedInverse) argument)
          (secondCompositionMaps argument argumentInComposition argumentInCylinder) =
          reparametrization
            (quotientPoint (normalizedInverse argument) normalizedImageMembership) := by
        exact forwardAtArgument
      _ = reparametrization
          (reparametrization.symm (quotientPoint argument argumentInCylinder)) := by
        rw [normalizedAtArgument]
      _ = quotientPoint argument argumentInCylinder := reparametrization.apply_symm_apply _
  obtain ⟨secondExactNeighborhood, secondExactOpen, imageInSecondExact,
      secondExactSubset, secondExactAgreement⟩ :=
    locally_eq_of_quotientPoint_eq isOpen_interior imageInSecondComposition
      (forwardContinuousAt.comp_of_eq normalizedContinuousAt normalizedAtBase)
      continuousAt_id (by rw [Function.comp_apply, normalizedAtBase]; rfl)
      secondCompositionMaps (fun argument _ membership => membership)
      secondCompositionQuotient
  have secondExactSmooth : ContDiffOn ℝ regularity.order
      (forwardLift ∘ normalizedInverse) secondExactNeighborhood :=
    secondCompositionSmooth.mono secondExactSubset
  have secondWithinDerivative :
      fderivWithin ℝ id cylinder (forwardLift point) =
        fderiv ℝ (forwardLift ∘ normalizedInverse) (forwardLift point) :=
    localExtension_fderivWithin uniqueDiffOn_cylinder forwardImageInCylinder secondExactOpen
      imageInSecondExact secondExactSmooth secondExactAgreement orderNonzero
  have secondDerivativeInverse :
      (fderiv ℝ forwardLift point).comp
          (fderiv ℝ normalizedInverse (forwardLift point)) =
        ContinuousLinearMap.id ℝ Vec := by
    have forwardDifferentiableAtNormalized :
        DifferentiableAt ℝ forwardLift (normalizedInverse (forwardLift point)) := by
      rw [normalizedAtBase]
      exact forwardDifferentiableAt
    calc
      (fderiv ℝ forwardLift point).comp
          (fderiv ℝ normalizedInverse (forwardLift point)) =
          fderiv ℝ (forwardLift ∘ normalizedInverse) (forwardLift point) := by
        simpa only [normalizedAtBase] using
          (fderiv_comp (forwardLift point) forwardDifferentiableAtNormalized
            normalizedDifferentiableAt).symm
      _ = fderivWithin ℝ id cylinder (forwardLift point) := secondWithinDerivative.symm
      _ = ContinuousLinearMap.id ℝ Vec :=
        fderivWithin_id (uniqueDiffOn_cylinder _ forwardImageInCylinder)
  exact ⟨normalizedInverse, normalizedDifferentiableAt,
    firstDerivativeInverse, secondDerivativeInverse⟩

theorem continuousLinearEquiv_of_two_sided_inverse
    (forward inverse : Vec →L[ℝ] Vec)
    (leftInverse : inverse.comp forward = ContinuousLinearMap.id ℝ Vec)
    (rightInverse : forward.comp inverse = ContinuousLinearMap.id ℝ Vec) :
    ∃ equivalence : Vec ≃L[ℝ] Vec,
      equivalence.toContinuousLinearMap = forward ∧
      equivalence.symm.toContinuousLinearMap = inverse := by
  have leftApply (point : Vec) : inverse (forward point) = point := by
    have equality := congrArg (fun mapping : Vec →L[ℝ] Vec => mapping point) leftInverse
    simpa using equality
  have rightApply (point : Vec) : forward (inverse point) = point := by
    have equality := congrArg (fun mapping : Vec →L[ℝ] Vec => mapping point) rightInverse
    simpa using equality
  have forwardInjective : Function.Injective forward := by
    intro first second equality
    rw [← leftApply first, ← leftApply second, equality]
  have forwardSurjective : Function.Surjective forward := by
    intro point
    exact ⟨inverse point, rightApply point⟩
  have kernelBottom : forward.ker = ⊥ := LinearMap.ker_eq_bot.mpr forwardInjective
  have rangeTop : forward.range = ⊤ := LinearMap.range_eq_top.mpr forwardSurjective
  let equivalence := ContinuousLinearEquiv.ofBijective forward kernelBottom rangeTop
  refine ⟨equivalence, ContinuousLinearEquiv.coe_ofBijective forward kernelBottom rangeTop, ?_⟩
  apply ContinuousLinearMap.ext
  intro point
  apply forwardInjective
  calc
    forward (equivalence.symm point) = point := equivalence.apply_symm_apply point
    _ = forward (inverse point) := (rightApply point).symm

/-- Exact `NG_Z06_DERIVATIVE`: the ambient derivative of every valid chosen
forward local lift is a continuous linear equivalence, with inverse the
derivative of a period-normalized inverse local lift at the forward image. -/
theorem localLiftDerivativeEquiv
    (regularity : Regularity) (admissible : regularity.admissible)
    (reparametrization : Reference ≃ Reference)
    (isReparametrization : IsReparametrization regularity reparametrization)
    (point : Vec) (pointInCylinder : point ∈ cylinder)
    (forwardNeighborhood : Set Vec) (forwardOpen : IsOpen forwardNeighborhood)
    (pointInForward : point ∈ forwardNeighborhood) (forwardLift : Vec → Vec)
    (forwardSmooth : ContDiffOn ℝ regularity.order forwardLift forwardNeighborhood)
    (forwardAgreement : ∀ argument ∈ forwardNeighborhood,
      ∀ membership : argument ∈ cylinder,
        ∃ imageMembership : forwardLift argument ∈ cylinder,
          quotientPoint (forwardLift argument) imageMembership =
            reparametrization (quotientPoint argument membership)) :
    ∃ (normalizedInverse : Vec → Vec) (derivativeEquiv : Vec ≃L[ℝ] Vec),
      DifferentiableAt ℝ normalizedInverse (forwardLift point) ∧
      derivativeEquiv.toContinuousLinearMap = fderiv ℝ forwardLift point ∧
      derivativeEquiv.symm.toContinuousLinearMap =
        fderiv ℝ normalizedInverse (forwardLift point) := by
  obtain ⟨normalizedInverse, normalizedDifferentiable,
      leftInverse, rightInverse⟩ :=
    localLift_fderiv_has_two_sided_inverse regularity admissible reparametrization
      isReparametrization point pointInCylinder forwardNeighborhood forwardOpen
      pointInForward forwardLift forwardSmooth forwardAgreement
  obtain ⟨derivativeEquiv, forwardDerivative, inverseDerivative⟩ :=
    continuousLinearEquiv_of_two_sided_inverse
      (fderiv ℝ forwardLift point) (fderiv ℝ normalizedInverse (forwardLift point))
      leftInverse rightInverse
  exact ⟨normalizedInverse, derivativeEquiv, normalizedDifferentiable,
    forwardDerivative, inverseDerivative⟩

end Grad.MainAssembly.TargetReparametrization
