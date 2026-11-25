module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoTermComparisonRestrictScalars
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Away
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open CategoryTheory Limits

universe v u

namespace GlobalTheory

section General

variable {ι : Type} [LinearOrder ι] {R : Type u} [CommRing R]

namespace Cube


omit [LinearOrder ι] in
theorem exists_smul_eq_zero_of_forall [Finite ι] (A : Cube.{max u v} ι R) (S : Submonoid R) {p : ℕ}
    (x : Term A p) (h : ∀ s, ∃ c ∈ S, c • x s = 0) : ∃ c ∈ S, c • x = 0 := by
  classical
  have := Fintype.ofFinite {s : Finset ι // s.card = p}
  choose c hcS hc using h
  refine ⟨∏ s, c s, S.prod_mem fun s _ => hcS s, funext fun s => ?_⟩
  rw [Pi.smul_apply, ← Finset.prod_erase_mul _ _ (Finset.mem_univ s), mul_smul, hc, smul_zero,
    Pi.zero_apply]

theorem exists_smul_eq_zero_of_d_eq_zero [Finite ι] (A : Cube.{max u v} ι R) (S : Submonoid R) (i : ι)
    (hA : ∀ s : Finset ι, i ∉ s → ∀ y, res A (Finset.subset_insert i s) y = 0 → ∃ c ∈ S, c • y = 0)
    {p : ℕ} (x : Term A p) (hx : d A p x = 0)
    (h0 : ∀ s : {s : Finset ι // s.card = p}, i ∈ s.1 → x s = 0) : ∃ c ∈ S, c • x = 0 := by
  refine exists_smul_eq_zero_of_forall A S x fun s => ?_
  by_cases hs : i ∈ s.1
  · exact ⟨1, S.one_mem, by rw [h0 s hs, smul_zero]⟩
  have h := congrFun hx ⟨insert i s.1, by rw [Finset.card_insert_of_notMem hs, s.2]⟩
  rw [d_apply_extend, Finset.sum_eq_single i, Pi.zero_apply, cubeSign_smul_eq_zero,
    res_congr A _ (Finset.erase_insert hs) _ (Finset.subset_insert i s.1),
    extend_apply_of_eq A x s.2] at h
  · exact hA s.1 hs _ h
  · intro j _ hji
    by_cases hc : ((insert i s.1).erase j).card = p
    · rw [extend_apply_of_eq A x hc, h0 _ (by simp [hji.symm]), map_zero, smul_zero]
    · rw [extend_apply_of_ne A x hc, map_zero, smul_zero]
  · simp

theorem exists_smul_eq_d [Finite ι] (A : Cube.{max u v} ι R) (S : Submonoid R) (i : ι)
    (hA : ∀ s : Finset ι, i ∉ s → ∀ y, res A (Finset.subset_insert i s) y = 0 → ∃ c ∈ S, c • y = 0)
    (hA' : ∀ s : Finset ι, i ∉ s → ∀ z, ∃ c ∈ S, ∃ y,
      res A (Finset.subset_insert i s) y = c • z)
    {p : ℕ} (x : Term A (p + 1)) (hx : d A (p + 1) x = 0) :
    ∃ c ∈ S, ∃ y, d A p y = c • x := by
  classical
  have := Fintype.ofFinite (Finset ι)
  have hy : ∀ s : Finset ι, ∃ c ∈ S, ∃ y : A.obj s, (i ∈ s → y = 0) ∧ (i ∉ s →
      res A (Finset.subset_insert i s) y =
        c • cubeSign (insert i s) i • extend A (p + 1) x (insert i s)) := by
    intro s
    by_cases hs : i ∈ s
    · exact ⟨1, S.one_mem, 0, fun _ => rfl, fun h => absurd hs h⟩
    · obtain ⟨c, hc, y, hy⟩ :=
        hA' s hs (cubeSign (insert i s) i • extend A (p + 1) x (insert i s))
      exact ⟨c, hc, y, fun h => absurd h hs, fun _ => hy⟩
  choose c hcS y hy0 hy1 using hy
  let y' : ∀ s, A.obj s := fun s => (∏ t ∈ Finset.univ.erase s, c t) • y s
  obtain ⟨e, heS, he⟩ := exists_smul_eq_zero_of_d_eq_zero A S i hA
    (d A p (fun s => y' s.1) - (∏ t, c t) • x) (by rw [map_sub, d_d, map_smul, hx]; simp) (by
      rintro ⟨t, ht⟩ hi
      obtain ⟨s, hs, rfl⟩ : ∃ s, i ∉ s ∧ t = insert i s :=
        ⟨t.erase i, by simp, (Finset.insert_erase hi).symm⟩
      rw [Pi.sub_apply, d_apply_eq_totalD A _ y' (fun _ => rfl), totalD_apply,
        Finset.sum_eq_single i,
        res_congr A _ (Finset.erase_insert hs) _ (Finset.subset_insert i s)]
      · simp only [y', map_smul]
        rw [hy1 s hs, smul_smul _ (c s), Finset.prod_erase_mul _ _ (Finset.mem_univ s), smul_comm,
          cubeSign_smul_smul, extend_apply_of_eq A x ht, Pi.smul_apply, sub_self]
      · intro j _ hji
        simp only [y']
        rw [hy0 _ (by simp [hji.symm]), smul_zero, map_zero, smul_zero]
      · simp)
  refine ⟨e * ∏ t, c t, S.mul_mem heS (S.prod_mem fun t _ => hcS t), e • (fun s => y' s.1 : Term A p), ?_⟩
  rw [smul_sub, sub_eq_zero] at he
  rw [map_smul, he, mul_smul]

end Cube

theorem smul_homologyπ_eq_zero (K : CochainComplex (ModuleCat.{v} R) ℕ) (q p : ℕ)
    (z : K.cycles p) (c : R) (y : K.X q) (h : (K.d q p).hom y = c • (K.iCycles p).hom z) :
    c • (K.homologyπ p).hom z = 0 := by
  have h1 : (K.toCycles q p).hom y = c • z := by
    apply (ModuleCat.mono_iff_injective (K.iCycles p)).1 inferInstance
    have := congr(($(K.toCycles_i q p)).hom y)
    exact this.trans (h.trans (map_smul _ _ _).symm)
  rw [← map_smul, ← h1]
  exact congr(($(K.toCycles_comp_homologyπ q p)).hom y)

theorem cubeComplex_exists_smul_homology_eq_zero [Finite ι] (A : Cube.{max u v} ι R) (S : Submonoid R)
    (i : ι)
    (hA : ∀ s : Finset ι, i ∉ s → ∀ y,
      Cube.res A (Finset.subset_insert i s) y = 0 → ∃ c ∈ S, c • y = 0)
    (hA' : ∀ s : Finset ι, i ∉ s → ∀ z, ∃ c ∈ S, ∃ y,
      Cube.res A (Finset.subset_insert i s) y = c • z)
    (p : ℕ) (x : (cubeComplex A).homology p) : ∃ c ∈ S, c • x = 0 := by
  obtain ⟨z, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((cubeComplex A).homologyπ p)).1 inferInstance x
  have hz : Cube.d A p (((cubeComplex A).iCycles p).hom z) = 0 := by
    have := (cubeComplex A).iCycles_d p (p + 1)
    rw [cubeComplex_d] at this
    exact congr(($this).hom z)
  cases p with
  | zero =>
    obtain ⟨c, hc, h⟩ := Cube.exists_smul_eq_zero_of_d_eq_zero A S i hA _ hz fun s hs => by
      rw [Finset.card_eq_zero.1 s.2] at hs
      simp at hs
    exact ⟨c, hc, smul_homologyπ_eq_zero _ 0 0 z c 0 ((map_zero _).trans h.symm)⟩
  | succ p =>
    obtain ⟨c, hc, y, h⟩ := Cube.exists_smul_eq_d A S i hA hA' _ hz
    refine ⟨c, hc, smul_homologyπ_eq_zero _ p (p + 1) z c y ?_⟩
    rw [cubeComplex_d]
    exact h

end General

section Away

variable {R : Type*} [CommRing R] {M N P : Type*} [AddCommGroup M] [AddCommGroup N]
  [AddCommGroup P] [Module R M] [Module R N] [Module R P]

theorem isUnit_algebraMap_end_of_dvd {a b : R} (h : a ∣ b)
    (hb : IsUnit (algebraMap R (Module.End R N) b)) :
    IsUnit (algebraMap R (Module.End R N) a) := by
  obtain ⟨c, rfl⟩ := h
  rw [map_mul] at hb
  exact ((Commute.isUnit_mul_iff (Algebra.commutes a _)).1 hb).1

theorem isUnit_powers_of_dvd {a b : R} (h : a ∣ b) (g : M →ₗ[R] N) [IsLocalizedModule.Away b g]
    (x : Submonoid.powers a) : IsUnit (algebraMap R (Module.End R N) x) := by
  obtain ⟨_, n, rfl⟩ := x
  rw [map_pow]
  exact (isUnit_algebraMap_end_of_dvd h (IsLocalizedModule.Away.isUnit_algebraMap g b)).pow n

theorem isLocalizedModule_away_of_comp {a b : R} (g : M →ₗ[R] N) (h : N →ₗ[R] P)
    [IsLocalizedModule.Away b g] [IsLocalizedModule.Away (a * b) (h ∘ₗ g)] :
    IsLocalizedModule.Away a h := by
  have hb := isUnit_powers_of_dvd (dvd_mul_left b a) (h ∘ₗ g)
  refine IsLocalizedModule.Away.mk_of_addCommGroup
    (isUnit_algebraMap_end_of_dvd (dvd_mul_right a b)
      (IsLocalizedModule.Away.isUnit_algebraMap (h ∘ₗ g) _)) (fun z => ?_) (fun y hy => ?_)
  · obtain ⟨n, m, hm⟩ := IsLocalizedModule.Away.surj (h ∘ₗ g) (a * b) z
    refine ⟨n, IsLocalizedModule.mk' g m (⟨b ^ n, n, rfl⟩ : Submonoid.powers b), ?_⟩
    apply ((Module.End.isUnit_iff _).1 (hb ⟨b ^ n, n, rfl⟩)).1
    simp only [Module.algebraMap_end_apply]
    rw [← map_smul, smul_smul, mul_comm, ← mul_pow, hm]
    exact congrArg h (IsLocalizedModule.mk'_cancel' g m (⟨b ^ n, n, rfl⟩ : Submonoid.powers b)).symm
  · obtain ⟨k, m, hm⟩ := IsLocalizedModule.Away.surj g b y
    have h0 : (h ∘ₗ g) m = (h ∘ₗ g) 0 := by
      rw [LinearMap.comp_apply, ← hm, map_smul, hy, smul_zero, map_zero]
    obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (a * b) h0
    refine ⟨n, ?_⟩
    apply IsLocalizedModule.smul_injective g (⟨b ^ (n + k), n + k, rfl⟩ : Submonoid.powers b)
    have := congrArg g hn
    rw [smul_zero, map_zero, map_smul, ← hm, smul_smul] at this
    change b ^ (n + k) • a ^ n • y = b ^ (n + k) • (0 : N)
    rw [smul_zero, smul_smul, show b ^ (n + k) * a ^ n = (a * b) ^ n * b ^ k by ring]
    exact this

end Away

section Loc

variable {ι : Type} {R : Type u} [CommRing R]

variable (f : ι → R) (M : Type v) [AddCommGroup M] [Module R M]

noncomputable def locRes {s t : Finset ι} (h : s ⊆ t) :
    LocalizedModule (.powers (∏ i ∈ s, f i)) M →ₗ[R] LocalizedModule (.powers (∏ i ∈ t, f i)) M :=
  LocalizedModule.lift _ (LocalizedModule.mkLinearMap _ M)
    (isUnit_powers_of_dvd (Finset.prod_dvd_prod_of_subset s t f h) (LocalizedModule.mkLinearMap _ M))

@[simp]
theorem locRes_mk_one {s t : Finset ι} (h : s ⊆ t) (m : M) :
    locRes f M h (LocalizedModule.mk m 1) = LocalizedModule.mk m 1 :=
  LocalizedModule.lift_mk_one _ _ _ m

theorem locRes_comp_mkLinearMap {s t : Finset ι} (h : s ⊆ t) :
    locRes f M h ∘ₗ LocalizedModule.mkLinearMap _ M = LocalizedModule.mkLinearMap _ M :=
  LocalizedModule.lift_comp _ _ _

theorem locRes_mk {s t : Finset ι} (h : s ⊆ t) (m : M) (a : Submonoid.powers (∏ i ∈ s, f i))
    (b : Submonoid.powers (∏ i ∈ t, f i)) (c : R) (hb : (b : R) = c * a) :
    locRes f M h (LocalizedModule.mk m a) = LocalizedModule.mk (c • m) b := by
  apply IsLocalizedModule.smul_injective (LocalizedModule.mkLinearMap _ M) b
  have h1 : (a : R) • LocalizedModule.mk m a = LocalizedModule.mk m 1 := by
    rw [LocalizedModule.smul'_mk]; exact LocalizedModule.mk_cancel a m
  have h2 : (b : R) • LocalizedModule.mk (c • m) b = LocalizedModule.mk (c • m) 1 := by
    rw [LocalizedModule.smul'_mk]; exact LocalizedModule.mk_cancel b _
  simp only [Submonoid.smul_def]
  rw [h2, hb, mul_smul, ← map_smul, h1, locRes_mk_one, LocalizedModule.smul'_mk]

theorem locRes_self (s : Finset ι) : locRes f M (subset_refl s) = LinearMap.id :=
  LocalizedModule.lift_unique _ _ _ _ rfl

theorem locRes_comp {s t w : Finset ι} (h : s ⊆ t) (h' : t ⊆ w) :
    locRes f M h' ∘ₗ locRes f M h = locRes f M (h.trans h') :=
  (LocalizedModule.lift_unique _ _ _ _ (by
    rw [LinearMap.comp_assoc, locRes_comp_mkLinearMap, locRes_comp_mkLinearMap])).symm

noncomputable def locCube : Cube.{max u v} ι R :=
  Cube.mk (fun s => ModuleCat.of R (LocalizedModule (.powers (∏ i ∈ s, f i)) M))
    (fun h => locRes f M h) (fun s x => congr($(locRes_self f M s) x))
    (fun h h' x => congr($(locRes_comp f M h h') x))

noncomputable def toLocCube (s : Finset ι) : M →ₗ[R] (locCube f M).obj s :=
  LocalizedModule.mkLinearMap _ M

instance isLocalizedModule_toLocCube (s : Finset ι) :
    IsLocalizedModule.Away (∏ i ∈ s, f i) (toLocCube f M s) :=
  localizedModuleIsLocalizedModule _

@[simp]
theorem res_toLocCube {s t : Finset ι} (h : s ⊆ t) (m : M) :
    Cube.res (locCube f M) h (toLocCube f M s m) = toLocCube f M t m :=
  locRes_mk_one f M h m



variable [LinearOrder ι] [Finite ι]

variable {f}


end Loc

end GlobalTheory
