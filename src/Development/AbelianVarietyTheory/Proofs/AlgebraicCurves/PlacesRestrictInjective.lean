module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HeightIntegralEstimates
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LaTIsPrime
public import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.IsUnitOfValEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.WeakApprox
import ReciprocityTheory.SemistableReduction.AlgAll
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.T0 IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.PlaceRestrict

open ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas

theorem val_aeval_eq_coeff {Ω U σ : Type} [Field Ω] [Field U] [Algebra Ω U]
    (w : AddValuation U (WithTop ℤ)) (t : σ → U) (ht : ∀ s, t s ∈ vRing w)
    (hind : letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap Ω U)
      AlgebraicIndependent (ResidueField ((vRing w).comap (algebraMap Ω U)))
        (fun s => residue (vRing w) ⟨t s, ht s⟩))
    (P : MvPolynomial σ Ω) (α : σ →₀ ℕ) (hα : α ∈ P.support)
    (hmin : ∀ β ∈ P.support, w (algebraMap Ω U (P.coeff α)) ≤ w (algebraMap Ω U (P.coeff β))) :
    w (MvPolynomial.aeval t P) = w (algebraMap Ω U (P.coeff α)) := by
  classical
  have hc : P.coeff α ≠ 0 := MvPolynomial.mem_support_iff.mp hα
  have key := val_eval_eq_zero w t ht hind (MvPolynomial.C (P.coeff α)⁻¹ * P) ?_ α ?_
  · have : MvPolynomial.aeval t P =
        algebraMap Ω U (P.coeff α) * MvPolynomial.aeval t (MvPolynomial.C (P.coeff α)⁻¹ * P) := by
      rw [map_mul, MvPolynomial.aeval_C, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]
    rw [this, AddValuation.map_mul, key, add_zero]
  · intro β
    rw [MvPolynomial.coeff_C_mul, map_mul, AddValuation.map_mul]
    by_cases hβ : β ∈ P.support
    · have h3 := hmin β hβ
      calc (0 : WithTop ℤ) = w (algebraMap Ω U (P.coeff α)⁻¹) + w (algebraMap Ω U (P.coeff α)) := by
            rw [← AddValuation.map_mul, ← map_mul, inv_mul_cancel₀ hc, map_one, AddValuation.map_one]
        _ ≤ _ := add_le_add le_rfl h3
    · rw [MvPolynomial.notMem_support_iff.mp hβ, map_zero, AddValuation.map_zero]
      simp
  · rw [MvPolynomial.coeff_C_mul, inv_mul_cancel₀ hc]

theorem val_aeval_congr {Ω U σ : Type} [Field Ω] [Field U] [Algebra Ω U]
    (w w' : AddValuation U (WithTop ℤ)) (t : σ → U) (ht : ∀ s, t s ∈ vRing w)
    (hind : letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap Ω U)
      AlgebraicIndependent (ResidueField ((vRing w).comap (algebraMap Ω U)))
        (fun s => residue (vRing w) ⟨t s, ht s⟩))
    (ht' : ∀ s, t s ∈ vRing w')
    (hind' : letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w') (algebraMap Ω U)
      AlgebraicIndependent (ResidueField ((vRing w').comap (algebraMap Ω U)))
        (fun s => residue (vRing w') ⟨t s, ht' s⟩))
    (hres : ∀ x : Ω, w (algebraMap Ω U x) = w' (algebraMap Ω U x))
    (P : MvPolynomial σ Ω) : w (MvPolynomial.aeval t P) = w' (MvPolynomial.aeval t P) := by
  classical
  by_cases hP : P = 0
  · subst hP; simp
  have hne : P.support.Nonempty := by
    obtain ⟨β, hβ⟩ := MvPolynomial.ne_zero_iff.mp hP
    exact ⟨β, MvPolynomial.mem_support_iff.mpr hβ⟩
  obtain ⟨α, hα, hmin⟩ := P.support.exists_min_image (fun β => w (algebraMap Ω U (P.coeff β))) hne
  rw [val_aeval_eq_coeff w t ht hind P α hα hmin, val_aeval_eq_coeff w' t ht' hind' P α hα
    (fun β hβ => by rw [← hres, ← hres]; exact hmin β hβ), hres]

theorem exists_orders {Ω X : Type} [Field Ω] (S : Set X) (hS : S.Finite)
    (v : X → AddValuation Ω (WithTop ℤ)) (hinj : Set.InjOn v S)
    (hn : ∀ w ∈ S, IsNormDiscrete (v w)) (n : X → ℤ) :
    ∃ g : Ω, g ≠ 0 ∧ ∀ w ∈ S, v w g = n w := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨w0, hw0⟩
  · exact ⟨1, one_ne_zero, by simp⟩
  haveI := hS.fintype
  let e := (Fintype.equivFin S).symm
  obtain ⟨g, hg⟩ := weak_approx_orders (fun i => v (e i)) (fun i => (hn _ (e i).2).1)
    (fun i => (hn _ (e i).2).2)
    (fun i j hij h => hij (e.injective (Subtype.ext (hinj (e i).2 (e j).2 h)))) (fun i => n (e i))
  have hg' : ∀ w ∈ S, v w g = n w := fun w hw => by
    have := hg (e.symm ⟨w, hw⟩)
    simpa using this
  exact ⟨g, wa_ne_zero_of_coe _ (hg' w0 hw0), hg'⟩

theorem exists_integral_lift {Ω X : Type} [Field Ω] (S : Set X) (hS : S.Finite)
    (v : X → AddValuation Ω (WithTop ℤ)) (hinj : Set.InjOn v S)
    (hn : ∀ w ∈ S, IsNormDiscrete (v w)) (w : X) (hw : w ∈ S) (a : Ω) (ha : 0 ≤ v w a) :
    ∃ l : Ω, (∀ w' ∈ S, 0 ≤ v w' l) ∧ 0 < v w (a - l) := by
  classical
  by_cases ha0 : a = 0
  · exact ⟨0, by simp, by simp [ha0]⟩
  have hm : ∀ x, ∃ m : ℤ, x ∈ S → v x a = m := fun x => by
    by_cases hx : x ∈ S
    · obtain ⟨m, hm⟩ := wa_exists_coe (v x) (hn x hx).1 ha0
      exact ⟨m, fun _ => hm⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose m hm using hm
  obtain ⟨s, hs0, hs⟩ := exists_orders S hS v hinj hn
    (fun x => if x = w then 1 else min (m x) 0 - 1)
  have hsw : v w s = ((1 : ℤ) : WithTop ℤ) := by simpa using hs w hw
  have h1w : v w (1 + s) = ((0 : ℤ) : WithTop ℤ) := by
    rw [AddValuation.map_add_eq_of_lt_left _ (by
      rw [AddValuation.map_one, hsw]; exact_mod_cast (zero_lt_one : (0 : ℤ) < 1)),
      AddValuation.map_one, WithTop.coe_zero]
  have h1s : (1 + s) ≠ 0 := wa_ne_zero_of_coe _ h1w
  have hmw : 0 ≤ m w := by
    rw [hm w hw] at ha; exact_mod_cast ha
  refine ⟨a / (1 + s), fun x hx => ?_, ?_⟩
  · by_cases hxw : x = w
    · subst hxw
      rw [wa_div _ (hm x hx) h1w]
      exact_mod_cast (by omega : (0 : ℤ) ≤ m x - 0)
    · have hsx : v x s = ((min (m x) 0 - 1 : ℤ) : WithTop ℤ) := by
        have := hs x hx
        rwa [ite_eq_right hxw] at this
      have h1x : v x (1 + s) = ((min (m x) 0 - 1 : ℤ) : WithTop ℤ) := by
        rw [AddValuation.map_add_eq_of_lt_right _ (by
          rw [AddValuation.map_one, hsx]
          exact_mod_cast (by omega : min (m x) 0 - 1 < (0 : ℤ))), hsx]
      rw [wa_div _ (hm x hx) h1x]
      exact_mod_cast (by omega : (0 : ℤ) ≤ m x - (min (m x) 0 - 1))
  · have : a - a / (1 + s) = a * s / (1 + s) := by field_simp; ring
    rw [this, wa_div _ (wa_mul _ (hm w hw) hsw) h1w]
    exact_mod_cast (by omega : (0 : ℤ) < m w + 1 - 0)

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

theorem exists_gauss_variables (d : Data K ι Ω WT A) (hd : d.AxH 𝒜)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (c : ι) (j0 : Fin (d.N + 1))
    (hw0 : d.w j0 c ≠ 0) :
    ∃ t : SVar d.D d.N → OmS (Ω c) d.D d.N,
      (∀ P : MvPolynomial (SVar d.D d.N) (Ω c), ∃ Q : MvPolynomial (SVar d.D d.N) (Ω c),
        MvPolynomial.aeval t Q = algebraMap _ (OmS (Ω c) d.D d.N) P) ∧
      ∀ w ∈ d.PlOver la c, (∀ j, 0 ≤ d.Wres c w (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) →
        ∃ ht : (∀ s, t s ∈ vRing w),
          letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap (Ω c) (OmS (Ω c) d.D d.N))
          AlgebraicIndependent
            (ResidueField ((vRing w).comap (algebraMap (Ω c) (OmS (Ω c) d.D d.N))))
            (fun s => residue (vRing w) ⟨t s, ht s⟩) := by
  obtain ⟨-, hψ, hgauss⟩ := d.gauss_variables_data hd la c j0 hw0
  refine ⟨_, fun P => ⟨_, hψ P⟩, fun w hw hrint => ?_⟩
  obtain ⟨ht, -, -, hG⟩ := hgauss w hw hrint
  exact ⟨ht, hG⟩

theorem wres_injOn (d : Data K ι Ω WT A) (hd : d.AxH 𝒜) (h : d.S1)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (c : ι) :
    Set.InjOn (d.Wres c) (d.PlOver la c) := by
  intro w hw w' hw' heq
  obtain ⟨-, -, j0, hj0, hint, -⟩ := d.admissible_over_prime hd h la c w hw
  obtain ⟨t, hsurj, hG⟩ := exists_gauss_variables d hd la c j0 hj0
  obtain ⟨ht, hi⟩ := hG w hw hint
  obtain ⟨ht', hi'⟩ := hG w' hw' (heq ▸ hint)
  have hres : ∀ x : Ω c, w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) x) =
      w' (algebraMap (Ω c) (OmS (Ω c) d.D d.N) x) := fun x => by
    change d.Wres c w x = d.Wres c w' x
    rw [heq]
  have hpoly : ∀ P : MvPolynomial (SVar d.D d.N) (Ω c),
      w (algebraMap _ (OmS (Ω c) d.D d.N) P) = w' (algebraMap _ (OmS (Ω c) d.D d.N) P) := by
    intro P
    obtain ⟨Q, hQ⟩ := hsurj P
    rw [← hQ]
    exact val_aeval_congr w w' t ht hi ht' hi' hres Q
  apply AddValuation.ext
  intro x
  obtain ⟨P, Q, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (SVar d.D d.N) (Ω c)) x
  rw [div_eq_mul_inv, AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_inv,
    AddValuation.map_inv, hpoly, hpoly]

theorem places_restrict_injective (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι]
    (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] (WT : Type) [AddCommGroup WT]
    (A : ι → Type) [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
    [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : Data K ι Ω WT A)
    (hd : d.AxH 𝒜) (h : d.S1) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (c : ι) :
    (d.PlOver la c).Finite ∧ Set.InjOn (d.Wres c) (d.PlOver la c) ∧
      (∀ n : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ) → ℤ,
        ∃ g : Ω c, g ≠ 0 ∧ ∀ w ∈ d.PlOver la c, d.Wres c w g = n w) ∧
      (∀ G : WT, ∃ e ∈ 𝒜 c G, e ≠ 0 ∧ ∀ w ∈ d.PlOver la c, d.ord c (d.Wres c w) G e = 0) ∧
      ∀ w ∈ d.PlOver la c, ∀ a : Ω c, 0 ≤ d.Wres c w a →
        ∃ l : Ω c, (∀ w' ∈ d.PlOver la c, 0 ≤ d.Wres c w' l) ∧ 0 < d.Wres c w (a - l) := by
  have hfin := (d.places_over_la hd h la c).1
  have hinj := wres_injOn d hd h la c
  have hadm : ∀ w ∈ d.PlOver la c, d.admitted c (d.Wres c w) := fun w hw => (d.admissible_over_prime hd h la c w hw).1
  have hn : ∀ w ∈ d.PlOver la c, IsNormDiscrete (d.Wres c w) := fun w hw => (hadm w hw).1
  refine ⟨hfin, hinj, exists_orders _ hfin _ hinj hn, fun G => ?_,
    exists_integral_lift _ hfin _ hinj hn⟩
  haveI : Nontrivial (𝒜 c G) := Module.nontrivial_of_finrank_pos (R := Ω c)
    (by rw [hd.finrank_one c G]; exact zero_lt_one)
  obtain ⟨e0, he0⟩ := exists_ne (0 : 𝒜 c G)
  have he0' : (e0 : A c) ≠ 0 := fun h0 => he0 (Subtype.ext h0)
  obtain ⟨g, hg0, hg⟩ := exists_orders _ hfin _ hinj hn
    (fun w => -d.ord c (d.Wres c w) G (e0 : A c))
  refine ⟨g • (e0 : A c), (𝒜 c G).smul_mem g e0.2, smul_ne_zero hg0 he0', fun w hw => ?_⟩
  have := hd.ord_smul c _ (hadm w hw) g e0.2 he0' hg0
  rw [hg w hw, ← WithTop.coe_add, neg_add_cancel] at this
  exact_mod_cast this

end GlobalTheory.PlaceRestrict
