module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsUnitTermZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdaptedBasisTestLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTorusTranslatesTwistedSumsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SumFCalculus
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Poinc.Sep.ExactSums

theorem sumI_fourier {V : Type} [CommRing V] [IsDomain V] (I : Ideal V) {n : ℕ} [NeZero n] {ω : V}
    (hω : IsPrimitiveRoot ω n) {G : Type} [AddCommGroup G] [Fintype G] (d : V) (hd : d * (Fintype.card G : V) = 1)
    {Ix : Type} (w : Ix → G → ZMod n) (hw : ∀ mu τ τ', w mu (τ + τ') = w mu τ + w mu τ') (κ : Ix)
    (x : Ix → V) (s : G → V) (h : ∀ τ, SumI I (fun mu => ω ^ (w mu τ).val * x mu) (s τ))
    (f : Ix → V) (hf1 : ∀ mu, (∀ τ, w mu τ = w κ τ) → f mu = x mu)
    (hf0 : ∀ mu, ¬ (∀ τ, w mu τ = w κ τ) → f mu = 0) :
    SumI I f (d * ∑ τ, ω ^ (-(w κ τ)).val * s τ) := by
  classical
  have pw : ∀ a b : ZMod n, ω ^ a.val * ω ^ b.val = ω ^ (a + b).val := fun a b => by
    rw [← pow_add, ZMod.val_add]
    conv_lhs => rw [← Nat.mod_add_div (a.val + b.val) n, pow_add, pow_mul, hω.pow_eq_one, one_pow, _root_.mul_one]
  have hchar : ∀ mu, ∑ τ, ω ^ (-(w κ τ)).val * ω ^ (w mu τ).val =
      if (∀ τ, w mu τ = w κ τ) then (Fintype.card G : V) else 0 := by
    intro mu
    simp_rw [pw]
    split_ifs with hmu
    · simp [hmu]
    · push Not at hmu
      obtain ⟨τ₀, h0⟩ := hmu
      set χ : G → V := fun τ => ω ^ (-(w κ τ) + w mu τ).val with hχ
      have hmul : ∀ τ, χ (τ + τ₀) = χ τ * χ τ₀ := fun τ => by
        simp only [χ, hw, pw]; congr 2; ring
      have hne : χ τ₀ ≠ 1 := by
        intro h1
        rw [hχ, hω.pow_eq_one_iff_dvd] at h1
        have hv : (-(w κ τ₀) + w mu τ₀).val ≠ 0 := by
          rw [ne_eq, ZMod.val_eq_zero]
          intro h
          exact h0 (neg_add_eq_zero.1 h).symm
        exact hv (Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt _))
      have hsum : ∑ τ, χ τ = χ τ₀ * ∑ τ, χ τ := by
        calc ∑ τ, χ τ = ∑ τ, χ (τ + τ₀) := (Equiv.sum_comp (Equiv.addRight τ₀) χ).symm
          _ = ∑ τ, χ τ * χ τ₀ := Finset.sum_congr rfl fun τ _ => hmul τ
          _ = χ τ₀ * ∑ τ, χ τ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => mul_comm _ _
      have h2 : (χ τ₀ - 1) * ∑ τ, χ τ = 0 := by rw [sub_mul, ← hsum, _root_.one_mul, sub_self]
      exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne)
  have hT : ∀ T : Finset G, SumI I (fun mu => ∑ τ ∈ T, ω ^ (-(w κ τ)).val * (ω ^ (w mu τ).val * x mu))
      (∑ τ ∈ T, ω ^ (-(w κ τ)).val * s τ) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact ⟨⊥, Submodule.fg_bot, Submodule.zero_mem _, fun _ => Submodule.zero_mem _, fun _ => ⟨∅, fun _ _ => by simp⟩⟩
    | insert a T ha ih =>
      simp only [Finset.sum_insert ha]
      exact GlobalTheory.AdicSum.sumI_add (GlobalTheory.AdicSum.sumI_map (LinearMap.mulLeft V (ω ^ (-(w κ a)).val)) (h a)) ih
  have hS := GlobalTheory.AdicSum.sumI_map (LinearMap.mulLeft V d) (hT Finset.univ)
  simp only [LinearMap.mulLeft_apply] at hS
  convert hS using 1
  funext mu
  have e : ∑ τ, ω ^ (-(w κ τ)).val * (ω ^ (w mu τ).val * x mu) =
      (∑ τ, ω ^ (-(w κ τ)).val * ω ^ (w mu τ).val) * x mu := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun τ _ => (_root_.mul_assoc _ _ _).symm
  rw [e, hchar]
  split_ifs with hmu
  · rw [hf1 mu hmu, ← _root_.mul_assoc, hd, _root_.one_mul]
  · rw [hf0 mu hmu, zero_mul, mul_zero]

theorem isClassSum_of_sumI {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ}
    {A : Type} [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (y : Φ.Y) (N : ℕ) (κ : Fin s → Φ.X y) (c : Φ.Q)
    {V' : Type} [CommRing V'] [IsLocalRing V'] (io : Φ.V y →+* V') (x : V') (f : (Fin s → Φ.X y) → V')
    (hf1 : ∀ mu, (∀ v, CongMod N (mu v) (κ v)) → f mu = io (Φ.term y mu c))
    (hf0 : ∀ mu, ¬ (∀ v, CongMod N (mu v) (κ v)) → f mu = 0)
    (h : SumI (maximalIdeal V') f x) : Φ.IsClassSum y N κ c io x := by
  classical
  intro j
  obtain ⟨M, -, -, -, hS⟩ := h
  obtain ⟨S₀, hS₀⟩ := hS j
  let P : (Fin s → Φ.X y) → Prop := fun mu => ∀ v, CongMod N (mu v) (κ v)
  let L := (PreModel.low_finite Φ y P j).toFinset
  let T := S₀ ∪ L
  refine ⟨T.filter P, fun mu hmu => (Finset.mem_filter.1 hmu).2, fun mu hP hn => ?_, ?_⟩
  · by_contra! hlt
    exact hn (Finset.mem_filter.2 ⟨Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 ⟨hP, hlt⟩), hP⟩)
  · have h1 := hS₀ T Finset.subset_union_left
    have h2 : ∑ mu ∈ T, f mu = io (∑ mu ∈ T.filter P, Φ.term y mu c) := by

      rw [map_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun mu _ => ?_
      split_ifs with hP
      · exact hf1 mu hP
      · exact hf0 mu hP
    rw [← h2]
    have hle : maximalIdeal V' ^ j • M ≤ maximalIdeal V' ^ j := by
      calc maximalIdeal V' ^ j • M ≤ maximalIdeal V' ^ j • (⊤ : Submodule V' V') := Submodule.smul_mono le_rfl le_top
        _ = maximalIdeal V' ^ j := by rw [smul_eq_mul, Ideal.mul_top]
    exact hle h1

theorem isPrimitiveRoot_map' {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) {n : ℕ}
    (hn : (n : V) ≠ 0) {ζ : R} (hζ : IsPrimitiveRoot ζ n) : IsPrimitiveRoot (φ ζ) n := by
  have : NeZero (n : V) := ⟨hn⟩
  have h₀ : 0 < n := Nat.pos_of_ne_zero fun e => hn (by rw [e, Nat.cast_zero])
  have h := (hζ.isRoot_cyclotomic h₀).map (f := φ)
  rw [Polynomial.map_cyclotomic] at h
  exact Polynomial.isRoot_cyclotomic_iff.1 h

end GlobalTheory.Poinc.Sep.ExactSums
