module

import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.IntSplitOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsoOfFrob
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CongruenceNumberRankThree
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

noncomputable section

namespace UpperTheory.V.Af

theorem finite_image_of_card_le {P Y : Type} (Sig : Set P) (Iso : P → P → Prop) (f : P → Y)
    (hiso : ∀ a ∈ Sig, ∀ b ∈ Sig, Iso a b → f a = f b) (N : ℕ)
    (hcard : ∀ S : Finset P, (∀ a ∈ S, a ∈ Sig) → (∀ a ∈ S, ∀ b ∈ S, Iso a b → a = b) → S.card ≤ N) :
    Finite ↥(f '' Sig) ∧ Nat.card ↥(f '' Sig) ≤ N := by
  classical
  have key : ∀ T : Finset Y, (↑T : Set Y) ⊆ f '' Sig → T.card ≤ N := by
    intro T hT
    have hpre : ∀ y : T, ∃ a, a ∈ Sig ∧ f a = y.1 := fun y => hT y.2
    choose g hgS hgf using hpre
    have hinj : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      rw [← hgf x, ← hgf y, hxy]
    have hS := hcard (Finset.univ.image g) ?_ ?_
    · rwa [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe] at hS
    · intro a ha
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp ha
      exact hgS y
    · intro a ha b hb hab
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hb
      have hxy := hiso _ (hgS x) _ (hgS y) hab
      rw [hgf x, hgf y] at hxy
      rw [Subtype.ext hxy]
  have hfin : (f '' Sig).Finite := by
    by_contra hinf
    obtain ⟨t, ht, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (N + 1)
    have := key t ht
    omega
  refine ⟨hfin.to_subtype, ?_⟩
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]
  exact key _ (by simp)

theorem exists_eigData {P W : Type} (Sig : Set P) (Iso : P → P → Prop) (sys : P → W → Multiset ℂ)
    (hiso : ∀ a ∈ Sig, ∀ b ∈ Sig, Iso a b → sys a = sys b) (N : ℕ)
    (hcard : ∀ S : Finset P, (∀ a ∈ S, a ∈ Sig) → (∀ a ∈ S, ∀ b ∈ S, Iso a b → a = b) → S.card ≤ N)
    (hconj : ∀ σ : ℂ ≃+* ℂ, ∀ a ∈ Sig, ∃ b ∈ Sig, ∀ v, sys b v = (sys a v).map σ)
    (w : W) {n q : ℕ} {m : Fin n → ℤ} {wt : ℤ} (hn : ∀ a ∈ Sig, (sys a w).card = n)
    (hpure : ∀ a ∈ Sig, ∀ b ∈ sys a w, ‖b‖ = (q : ℝ) ^ (-(wt : ℝ) / 2))
    (hint : ∀ a ∈ Sig, SlopesIn q m (sys a w)) :
    ∃ D : EigData n q m wt, Nat.card D.S ≤ N ∧ ∃ cl : ↥Sig → D.S, (∀ a b, cl a = cl b → sys a = sys b) ∧
      ∀ a, (D.β (cl a)).map (·⁻¹) = sys a w := by
  obtain ⟨hfin, hN⟩ := finite_image_of_card_le Sig Iso sys hiso N hcard
  refine ⟨⟨↥(sys '' Sig), hfin, fun s => (s.1 w).map (·⁻¹), ?_, ?_, ?_, ?_, ?_⟩, hN,
    fun a => ⟨sys a, a, a.2, rfl⟩, fun a b h => congrArg Subtype.val h, fun a => ?_⟩
  · rintro ⟨_, a, ha, rfl⟩
    simpa using hn a ha
  · intro σ
    have hmem : ∀ s : ↥(sys '' Sig), (fun v => (s.1 v).map σ) ∈ sys '' Sig := by
      rintro ⟨_, a, ha, rfl⟩
      obtain ⟨b, hb, h⟩ := hconj σ a ha
      exact ⟨b, hb, funext h⟩
    let F : ↥(sys '' Sig) → ↥(sys '' Sig) := fun s => ⟨_, hmem s⟩
    have hF : Function.Injective F := by
      intro s s' h
      refine Subtype.ext (funext fun v => ?_)
      exact Multiset.map_injective σ.injective (congrFun (congrArg Subtype.val h) v)
    refine ⟨Equiv.ofBijective F (Finite.injective_iff_bijective.1 hF), fun s => ?_⟩
    simp [F, Multiset.map_map]
  · rintro ⟨_, a, ha, rfl⟩ b hb
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hb
    rw [norm_inv, hpure a ha c hc, ← Real.rpow_neg (Nat.cast_nonneg q)]
    congr 1
    ring
  · rintro k hk ⟨_, a, ha, rfl⟩ b hb
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hb
    exact (hint a ha c hc).1 k hk
  · rintro k hk ⟨_, a, ha, rfl⟩ b hb
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hb
    rw [inv_inv]
    exact (hint a ha c hc).2 k hk
  · simp [Multiset.map_map]


open NumberField IsDedekindDomain in
theorem natCast_notMem_of_not_dvd {F : Type} [Field F] [NumberField F] {p M : ℕ} (hp : p.Prime)
    {w : HeightOneSpectrum (𝓞 F)} (hw : (p : 𝓞 F) ∈ w.asIdeal) (hM : ¬ p ∣ M) : (M : 𝓞 F) ∉ w.asIdeal := by
  intros
  apply _root_.Formalism.L2.G.natCast_notMem <;> assumption


open NumberField IsDedekindDomain in
theorem eventually_natCast_notMem {F : Type} [Field F] [NumberField F] {M : ℕ} (hM : M ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, (M : 𝓞 F) ∉ w.asIdeal := by
  apply _root_.GlobalTheory.GalChar.away_ae <;> assumption

end UpperTheory.V.Af
