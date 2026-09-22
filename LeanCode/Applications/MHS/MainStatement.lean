import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Topology.Instances.AddCircle.Defs

noncomputable section

open Set
open scoped ContDiff

namespace Grad.MainTarget

abbrev Vec := EuclideanSpace ℝ (Fin 3)
abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev CellCircle := AddCircle (2 * Real.pi)
abbrev ClosedDisk := {point : Plane // ‖point‖ ≤ 1}
abbrev Reference := ClosedDisk × CellCircle
abbrev Torus := CellCircle × CellCircle

def vector (first second third : ℝ) : Vec :=
  WithLp.toLp 2 ![first, second, third]

def planarPart (point : Vec) : Plane := WithLp.toLp 2 ![point 0, point 1]

def cylinder : Set Vec := {point | ‖planarPart point‖ ≤ 1}

def fundamentalCylinder : Set Vec :=
  {point | point ∈ cylinder ∧ 0 ≤ point 2 ∧ point 2 ≤ 2 * Real.pi}

def quotientPoint (point : Vec) (membership : point ∈ cylinder) : Reference :=
  (⟨planarPart point, membership⟩, (point 2 : CellCircle))

def periodicLift {Target : Type*} [Zero Target] (mapping : Reference → Target)
    (point : Vec) : Target := by
  classical
  exact if membership : point ∈ cylinder then mapping (quotientPoint point membership) else 0

inductive Regularity where
  | finite (order : ℕ)
  | smooth

def Regularity.order : Regularity → ℕ∞ω
  | .finite order => order
  | .smooth => ∞

def Regularity.predecessor : Regularity → Regularity
  | .finite order => .finite (order - 1)
  | .smooth => .smooth

def Regularity.admits (regularity : Regularity) (order : ℕ) : Prop :=
  (order : ℕ∞ω) ≤ regularity.order

def Regularity.admissible : Regularity → Prop
  | .finite order => 3 ≤ order
  | .smooth => True

def HasLocalExtensions {Domain Target : Type*}
    [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (regularity : Regularity) (mapping : Domain → Target) (domain : Set Domain) : Prop :=
  ∀ point ∈ domain,
    ∃ neighborhood : Set Domain, IsOpen neighborhood ∧ point ∈ neighborhood ∧
      ∃ extension : Domain → Target,
        ContDiffOn ℝ regularity.order extension neighborhood ∧
        Set.EqOn extension mapping (neighborhood ∩ domain)

def HasRegularity {Target : Type*} [NormedAddCommGroup Target]
    [NormedSpace ℝ Target] (regularity : Regularity)
    (mapping : Reference → Target) : Prop :=
  HasLocalExtensions regularity (periodicLift mapping) cylinder

def IsEmbeddingOfRegularity (regularity : Regularity)
    (mapping : Reference → Vec) : Prop :=
  HasRegularity regularity mapping ∧
  Topology.IsEmbedding mapping ∧
  ∀ point ∈ cylinder,
    Function.Injective (fderivWithin ℝ (periodicLift mapping) cylinder point)

structure Representative where
  position : Reference → Vec
  magnetic : Reference → Vec
  pressure : Reference → ℝ

def IsConfiguration (regularity : Regularity) (configuration : Representative) : Prop :=
  IsEmbeddingOfRegularity regularity configuration.position ∧
  HasRegularity regularity.predecessor configuration.magnetic ∧
  HasRegularity regularity configuration.pressure

abbrev Configuration (regularity : Regularity) :=
  {configuration : Representative // IsConfiguration regularity configuration}

def jets {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (regularity : Regularity) (mapping : Reference → Target) :
    ∀ order : {order : ℕ // regularity.admits order},
      UniformFun fundamentalCylinder
        (ContinuousMultilinearMap ℝ (fun _ : Fin order.val => Vec) Target) :=
  fun order => UniformFun.ofFun fun point =>
    iteratedFDerivWithin ℝ order.val (periodicLift mapping) cylinder point

instance configurationTopology (regularity : Regularity) :
    TopologicalSpace (Configuration regularity) :=
  TopologicalSpace.induced
    (fun configuration : Configuration regularity =>
      (jets regularity configuration.val.position,
       jets regularity.predecessor configuration.val.magnetic,
       jets regularity configuration.val.pressure)) inferInstance

def HasRegularLocalLifts (regularity : Regularity) (mapping : Reference → Reference) : Prop :=
  ∀ point ∈ cylinder,
    ∃ neighborhood : Set Vec, IsOpen neighborhood ∧ point ∈ neighborhood ∧
      ∃ localLift : Vec → Vec,
        ContDiffOn ℝ regularity.order localLift neighborhood ∧
        ∀ argument ∈ neighborhood, ∀ membership : argument ∈ cylinder,
          ∃ imageMembership : localLift argument ∈ cylinder,
            quotientPoint (localLift argument) imageMembership =
              mapping (quotientPoint argument membership)

def IsReparametrization (regularity : Regularity)
    (reparametrization : Reference ≃ Reference) : Prop :=
  HasRegularLocalLifts regularity reparametrization ∧
  HasRegularLocalLifts regularity reparametrization.symm

def Related (regularity : Regularity)
    (first second : Configuration regularity) : Prop :=
  ∃ (spatialScale amplitude : ℝ) (orthogonal : Vec ≃ₗᵢ[ℝ] Vec)
    (translation : Vec) (pressureOffset : ℝ)
    (reparametrization : Reference ≃ Reference),
    0 < spatialScale ∧ amplitude ≠ 0 ∧
    IsReparametrization regularity reparametrization ∧
    ∀ point : Reference,
      second.val.position point =
        spatialScale • orthogonal (first.val.position (reparametrization point)) + translation ∧
      second.val.magnetic point =
        amplitude • orthogonal (first.val.magnetic (reparametrization point)) ∧
      second.val.pressure point =
        amplitude ^ 2 * first.val.pressure (reparametrization point) + pressureOffset

def Moduli (regularity : Regularity) := Quot (Related regularity)

def moduliClass (regularity : Regularity) : Configuration regularity → Moduli regularity :=
  Quot.mk (Related regularity)

instance moduliTopology (regularity : Regularity) : TopologicalSpace (Moduli regularity) :=
  TopologicalSpace.coinduced (moduliClass regularity) inferInstance

def basisVector (coordinate : Fin 3) : Vec :=
  WithLp.toLp 2 (Pi.single coordinate 1)

def gradient (pressure : Vec → ℝ) (point : Vec) : Vec :=
  WithLp.toLp 2 fun coordinate => fderiv ℝ pressure point (basisVector coordinate)

def cross (first second : Vec) : Vec :=
  vector (first 1 * second 2 - first 2 * second 1)
    (first 2 * second 0 - first 0 * second 2)
    (first 0 * second 1 - first 1 * second 0)

def curl (magnetic : Vec → Vec) (point : Vec) : Vec :=
  vector
    ((fderiv ℝ magnetic point (basisVector 1)) 2 -
      (fderiv ℝ magnetic point (basisVector 2)) 1)
    ((fderiv ℝ magnetic point (basisVector 2)) 0 -
      (fderiv ℝ magnetic point (basisVector 0)) 2)
    ((fderiv ℝ magnetic point (basisVector 0)) 1 -
      (fderiv ℝ magnetic point (basisVector 1)) 0)

def divergence (magnetic : Vec → Vec) (point : Vec) : ℝ :=
  ∑ coordinate : Fin 3, (fderiv ℝ magnetic point (basisVector coordinate)) coordinate

def SmoothNear {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (body : Set Vec) (mapping : Vec → Target) : Prop :=
  ∃ neighborhood : Set Vec,
    IsOpen neighborhood ∧ body ⊆ neighborhood ∧ ContDiffOn ℝ ∞ mapping neighborhood

def TangentTo (surface : Set Vec) (point velocity : Vec) : Prop :=
  ∃ curve : ℝ → Vec,
    ContDiff ℝ ∞ curve ∧ curve 0 = point ∧
    (∀ time, curve time ∈ surface) ∧ fderiv ℝ curve 0 1 = velocity

def roundAxis (radius : ℝ) : Set Vec :=
  Set.range fun angle : ℝ => vector (radius * Real.cos angle) (radius * Real.sin angle) 0

def rotation (angle : ℝ) (point : Vec) : Vec :=
  vector (Real.cos angle * point 0 - Real.sin angle * point 1)
    (Real.sin angle * point 0 + Real.cos angle * point 1) (point 2)

def SignedStabilizes (body : Set Vec) (magnetic : Vec → Vec) (pressure : Vec → ℝ)
    (orthogonal : Vec ≃ₗᵢ[ℝ] Vec) (translation : Vec) : Prop :=
  let motion := fun point => orthogonal point + translation
  motion '' body = body ∧
  (∀ point ∈ body, pressure (motion point) = pressure point) ∧
  ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧
    ∀ point ∈ body, magnetic (motion point) = sign • orthogonal (magnetic point)

def torusLift (parametrization : Torus → Vec) (point : Plane) : Vec :=
  parametrization ((point 0 : CellCircle), (point 1 : CellCircle))

def IsEmbeddedTorus (surface : Set Vec) : Prop :=
  ∃ parametrization : Torus → Vec,
    ContDiff ℝ ∞ (torusLift parametrization) ∧
    Topology.IsEmbedding parametrization ∧ Set.range parametrization = surface ∧
    ∀ point : Plane, Function.Injective (fderiv ℝ (torusLift parametrization) point)

def pressureLevel (body : Set Vec) (pressure : Vec → ℝ) (value : ℝ) : Set Vec :=
  {point | point ∈ body ∧ pressure point = value}

def IsRegularLevel (body : Set Vec) (pressure : Vec → ℝ) (value : ℝ) : Prop :=
  ∀ point ∈ pressureLevel body pressure value, fderiv ℝ pressure point ≠ 0

abbrev FoliationDomain := Set.Ioc (0 : ℝ) 1 × Torus

def foliationCylinder : Set Vec := {point | point 0 ∈ Set.Ioc (0 : ℝ) 1}

def foliationLift (parametrization : FoliationDomain → Vec) (point : Vec) : Vec := by
  classical
  exact if membership : point ∈ foliationCylinder then
    parametrization (⟨point 0, membership⟩, (point 1 : CellCircle), (point 2 : CellCircle))
    else 0

def IsPressureFoliation (body axis : Set Vec) (pressure : Vec → ℝ) : Prop :=
  ∃ parametrization : FoliationDomain → Vec,
    HasLocalExtensions .smooth (foliationLift parametrization) foliationCylinder ∧
    Topology.IsEmbedding parametrization ∧ Set.range parametrization = body \ axis ∧
    (∀ point ∈ foliationCylinder,
      Function.Injective (fderivWithin ℝ (foliationLift parametrization) foliationCylinder point)) ∧
    (∀ radius : Set.Ioc (0 : ℝ) 1, ∃ value : ℝ,
      IsRegularLevel body pressure value ∧
      Set.range (fun angles : Torus => parametrization (radius, angles)) =
        pressureLevel body pressure value) ∧
    Set.range (fun angles : Torus => parametrization (⟨1, zero_lt_one, le_rfl⟩, angles)) =
      frontier body

def PhysicalConclusions (configuration : Representative) (cellLength : ℝ)
    (period : ℕ) : Prop :=
  let body := Set.range configuration.position
  let axis := roundAxis (period * cellLength)
  IsConfiguration .smooth configuration ∧
  ∃ (magnetic : Vec → Vec) (pressure : Vec → ℝ),
    SmoothNear body magnetic ∧ SmoothNear body pressure ∧
    (∀ point : Reference,
      magnetic (configuration.position point) = configuration.magnetic point ∧
      pressure (configuration.position point) = configuration.pressure point) ∧
    (∀ point ∈ interior body,
      cross (magnetic point) (curl magnetic point) + gradient pressure point = 0 ∧
      divergence magnetic point = 0) ∧
    (∀ point ∈ frontier body, TangentTo (frontier body) point (magnetic point)) ∧
    axis ⊆ interior body ∧
    {point | point ∈ body ∧ fderiv ℝ pressure point = 0} = axis ∧
    (∀ point ∈ body, magnetic point = 0 ↔ point ∈ axis) ∧
    (∀ value, (pressureLevel body pressure value).Nonempty →
      IsRegularLevel body pressure value → IsEmbeddedTorus (pressureLevel body pressure value)) ∧
    (∀ point ∈ body \ axis, IsRegularLevel body pressure (pressure point)) ∧
    IsPressureFoliation body axis pressure ∧
    (∀ (orthogonal : Vec ≃ₗᵢ[ℝ] Vec) (translation : Vec),
      SignedStabilizes body magnetic pressure orthogonal translation ↔
      ∃ rotationIndex : ℕ, rotationIndex < period ∧
        ∀ point : Vec, orthogonal point + translation =
          rotation (2 * Real.pi * rotationIndex / period) point)

def SmoothRepresentatives (interval : Set ℝ) (family : interval → Representative) : Prop :=
  ∃ parameterNeighborhood : Set ℝ, IsOpen parameterNeighborhood ∧
    interval ⊆ parameterNeighborhood ∧
    ∃ extension : ℝ → Representative,
      (∀ parameter : interval, extension parameter.val = family parameter) ∧
      HasLocalExtensions .smooth
        (fun argument : ℝ × Vec => periodicLift (extension argument.1).position argument.2)
        (parameterNeighborhood ×ˢ cylinder) ∧
      HasLocalExtensions .smooth
        (fun argument : ℝ × Vec => periodicLift (extension argument.1).magnetic argument.2)
        (parameterNeighborhood ×ˢ cylinder) ∧
      HasLocalExtensions .smooth
        (fun argument : ℝ × Vec => periodicLift (extension argument.1).pressure argument.2)
        (parameterNeighborhood ×ˢ cylinder)

def ModuliCurve (regularity : Regularity) (interval : Set ℝ)
    (family : interval → Representative) : Prop :=
  ∃ validity : ∀ parameter, IsConfiguration regularity (family parameter),
    let curve := fun parameter => moduliClass regularity ⟨family parameter, validity parameter⟩
    Continuous curve ∧ Function.Injective curve ∧
    ∀ parameter : interval, parameter.val ∈ interior interval →
      ¬ IsOpen ({curve parameter} : Set (Moduli regularity))

def mainTheoremStatement : Prop :=
  ∀ cellLength : ℝ, 0 < cellLength →
    ∃ (rho delta alpha lower upper : ℝ) (firstPeriod : ℕ),
      0 < rho ∧ rho < 1 / 4 ∧ delta ≠ 0 ∧
      (∀ multiple : ℤ, alpha ≠ (Real.pi / 2) * multiple) ∧
      0 < lower ∧ lower < upper ∧ upper < 1 / 2 ∧ 1 ≤ firstPeriod ∧
      ∃ family : ℕ → Set.Icc lower upper → Representative,
        ∀ period : ℕ, firstPeriod ≤ period →
          SmoothRepresentatives (Set.Icc lower upper) (family period) ∧
          (∀ parameter, PhysicalConclusions (family period parameter) cellLength period) ∧
          (∀ regularity, regularity.admissible →
            ModuliCurve regularity (Set.Icc lower upper) (family period))

end Grad.MainTarget
