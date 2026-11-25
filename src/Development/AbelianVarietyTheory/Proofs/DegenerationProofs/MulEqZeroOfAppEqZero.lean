module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSectionEqMulOfVanishingModElement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
open TopologicalSpace

namespace GlobalTheory.SquareZero


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open TopologicalSpace in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.SquareZero.mul_eq_zero_of_app_eq_zero : ∀ (A A' : Type) [CommRing A] [CommRing A']
    (g : A →+* A'), Function.Surjective g → RingHom.ker g ^ 2 = ⊥ → ∀ (X X' : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of A')) (β : X' ⟶ X),
    IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ (W : X.Opens) (x y : Γ(X, W)),
    (β.app W).hom x = 0 → (β.app W).hom y = 0 → x * y = 0 := by
  intro A A' _ _ g hg hsq X X' f f' β hpb W x y hx hy
  apply TopCat.Presheaf.section_ext X.sheaf W (x * y) 0
  intro p hp
  obtain ⟨V, hVaff, hpV, hVW⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hp
  have hres : ∀ z : Γ(X, W), (β.app W).hom z = 0 →
      _root_.GlobalTheory.AbLaw.rs X hVW z ∈
        Ideal.map (_root_.GlobalTheory.SmallExtLift.cst f V) (RingHom.ker g) := fun z hz =>
    _root_.GlobalTheory.SmallExtLift.mem_of_app_eq_zero hg hpb hVaff _
      (by rw [_root_.GlobalTheory.SectionKernel.app_rs, hz, map_zero])
  have hzero : _root_.GlobalTheory.AbLaw.rs X hVW (x * y) = 0 := by
    rw [map_mul]
    have hmem := Ideal.mul_mem_mul (hres x hx) (hres y hy)
    rw [← Ideal.map_mul, ← pow_two, hsq, Ideal.map_bot, Ideal.mem_bot] at hmem
    exact hmem
  have h1 := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVW) p hpV (x * y)
  have h2 := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVW) p hpV 0
  change X.presheaf.germ W p hp (x * y) = X.presheaf.germ W p hp 0
  rw [← h1, ← h2, map_zero]
  exact congrArg _ hzero

end GlobalTheory.SquareZero
