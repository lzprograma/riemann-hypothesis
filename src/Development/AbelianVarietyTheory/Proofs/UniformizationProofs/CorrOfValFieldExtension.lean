module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuesNatural
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

private theorem stalkMap_injective_of_flat' {Y Z : Scheme.{0}} (ρ : Z ⟶ Y) [Flat ρ] (z : Z) :
    Function.Injective (ρ.stalkMap z).hom := by

  let _ := (ρ.stalkMap z).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (ρ z)) (Z.presheaf.stalk z) := Flat.stalkMap ρ z
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (ρ z)) (Z.presheaf.stalk z)) :=
    (by infer_instance : IsLocalHom (ρ.stalkMap z).hom)
  have : Module.FaithfullyFlat (Y.presheaf.stalk (ρ z)) (Z.presheaf.stalk z) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (ρ z)) (Z.presheaf.stalk z)

theorem corr_of_val_flat_surjective {X Y Z : Scheme.{0}} (ρ : Z ⟶ Y) [Flat ρ] [Surjective ρ] {L : LB X}
    (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)}
    {ε' : K' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : ∀ z J, Good L z J → val t ρ z J = val t' ρ z J) : LB.Gen.Corr L φ ε φ' ε' t t' := by

  have : Epi ρ := Flat.epi_of_flat_of_surjective ρ
  refine corr_of_val hL fun y J hJ => ?_
  obtain ⟨z, rfl⟩ := ρ.surjective y
  obtain ⟨J', hJ', hJJ'⟩ := exists_good L hL z (fun ψ : Y ⟶ X => ρ ≫ ψ) J
    (fun a b hab => congrArg J ((cancel_epi ρ).1 hab)) (fun ψ => by simpa using hJ ψ)
  have hpull : (fun ψ : Y ⟶ X => J' (ρ ≫ ψ)) = J := funext hJJ'
  have e₁ := (values_natural X Y Y Z L K φ ε (𝟙 Y) ρ z J' hJ').2.2.1 t
  have e₂ := (values_natural X Y Y Z L K' φ' ε' (𝟙 Y) ρ z J' hJ').2.2.1 t'
  rw [Category.comp_id, hpull] at e₁ e₂

  apply Units.ext
  apply stalkMap_injective_of_flat' ρ z
  rw [← e₁, ← e₂, h z J' hJ']

theorem corr_of_val_field_extension : ∀ (K₀ F : Type) [Field K₀] [Field F] (f : K₀ →+* F) (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Spec (CommRingCat.of K₀) ⟶ X)) (ε : K → ℤ) (φ' : K' → (Spec (CommRingCat.of K₀) ⟶ X)) (ε' : K' → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')), (∀ z J, Good L z J → val t (Spec.map (CommRingCat.ofHom f)) z J = val t' (Spec.map (CommRingCat.ofHom f)) z J) → LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro K₀ F _ _ f X L hL K K' _ _ φ ε φ' ε' t t' h

  have hff : (CommRingCat.ofHom f).hom.FaithfullyFlat := by
    let _ := f.toAlgebra
    show Module.FaithfullyFlat K₀ F
    infer_instance
  obtain ⟨h₁, h₂⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom f)).2 hff
  exact corr_of_val_flat_surjective (Spec.map (CommRingCat.ofHom f)) hL h

end GlobalTheory
