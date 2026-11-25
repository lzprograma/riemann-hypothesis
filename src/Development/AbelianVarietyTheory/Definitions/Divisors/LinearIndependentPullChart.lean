module

public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiRegularAlongOfEtale
public import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentBasisCoords
public import Development.AbelianVarietyTheory.Definitions.Divisors.NoCommonZeroCombVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndepBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

@[expose] public section

noncomputable section

namespace GlobalTheory.HermTools

open NumberField

variable {K E : Type*} [Field K] [Field E] {X X' : Type*} [AddCommGroup X] [Module K X] [AddCommGroup X']
  [Module E X'] {j : K →+* E} (ι : X →ₛₗ[j] X')

def extSpace (V : Submodule K X) : Submodule E X' := Submodule.span E (ι '' V)

def extMap (V : Submodule K X) : V →ₛₗ[j] extSpace ι V :=
  (ι.domRestrict V).codRestrict _ fun x => Submodule.subset_span ⟨x, x.2, rfl⟩

theorem isExtension_extMap
    (h : ∀ (n : ℕ) (v : Fin n → X), LinearIndependent K v → LinearIndependent E fun i => ι (v i))
    (V : Submodule K X) : IsExtension (extMap ι V) := by
  refine ⟨fun n v hv => .of_comp (extSpace ι V).subtype (h n _ (hv.map' V.subtype V.ker_subtype)), ?_⟩
  refine Submodule.map_injective_of_injective (extSpace ι V).injective_subtype ?_
  rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
  exact congrArg _ (Set.image_eq_range ι V).symm

variable [Module (𝓞 K) X] [IsScalarTower (𝓞 K) K X] [Module (𝓞 E) X'] [IsScalarTower (𝓞 E) E X']

def extLat (M : Submodule (𝓞 K) X) : Submodule (𝓞 E) X' := Submodule.span (𝓞 E) (ι '' M)

theorem extLat_span (S : Set X) : extLat ι (Submodule.span (𝓞 K) S) = Submodule.span (𝓞 E) (ι '' S) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => exact map_zero ι ▸ zero_mem _
  | add a b _ _ ha hb => exact map_add ι a b ▸ add_mem ha hb
  | smul c a _ ha =>
    rw [← algebraMap_smul K, map_smulₛₗ]
    exact algebraMap_smul E (RingOfIntegers.mapRingHom j c) (ι a) ▸ Submodule.smul_mem _ _ ha

theorem fg_extLat {M : Submodule (𝓞 K) X} (h : M.FG) : (extLat ι M).FG := by
  obtain ⟨S, rfl⟩ := h
  exact extLat_span ι S ▸ Submodule.fg_span (S.finite_toSet.image ι)


variable {ι} in
theorem IsExtension.span_extLat (hι : IsExtension ι) {M : Submodule (𝓞 K) X}
    (h : Submodule.span K (M : Set X) = ⊤) : Submodule.span E (extLat ι M : Set X') = ⊤ := by
  refine top_le_iff.1 (hι.span.ge.trans (Submodule.span_le.2 ?_))
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ Submodule.span K (M : Set X) := h ▸ trivial
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (Submodule.subset_span ⟨x, hx, rfl⟩)
  | zero => exact map_zero ι ▸ zero_mem _
  | add a b _ _ ha hb => exact map_add ι a b ▸ add_mem ha hb
  | smul c a _ ha => exact map_smulₛₗ ι c a ▸ Submodule.smul_mem _ _ ha

structure IsFull (M : Submodule (𝓞 K) X) : Prop where

  fg : M.FG

  span : Submodule.span K (M : Set X) = ⊤

variable {ι} {M : Submodule (𝓞 K) X}

theorem IsFull.finiteDimensional (h : IsFull M) : FiniteDimensional K X := by
  obtain ⟨⟨S, rfl⟩, h⟩ := h
  rw [Submodule.span_span_of_tower] at h
  exact ⟨S, h⟩

theorem IsFull.latRank_eq [NumberField K] (h : IsFull M) : ReciprocityTheory.GeometryOfNumbersTheory.latRank K M = Module.finrank K X := by
  rw [ReciprocityTheory.GeometryOfNumbersTheory.latRank, h.span, finrank_top]

theorem IsFull.extLat (h : IsFull M) (hι : IsExtension ι) : IsFull (extLat ι M) :=
  ⟨fg_extLat ι h.fg, hι.span_extLat h.span⟩

theorem isFull_span {n : Type*} [Finite n] (b : Module.Basis n K X) :
    IsFull (Submodule.span (𝓞 K) (Set.range b)) :=
  ⟨Submodule.fg_span (Set.finite_range b), by rw [Submodule.span_span_of_tower, b.span_eq]⟩

end GlobalTheory.HermTools

namespace GlobalTheory.Vanishing

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX isPushout_sections)
open GlobalTheory.LB GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Points
open H0
open scoped ComplexOrder

variable {Y T : Scheme.{0}}

section Field

variable {k E : Type} [Field k] [Field E] {p : Y ⟶ Sp k} {B : LB Y} {O O' : Y.Opens}

instance H0.moduleInt : Module (𝓞 k) (H0 p B O) := Module.compHom _ (algebraMap (𝓞 k) k)

instance H0.isScalarTowerInt : IsScalarTower (𝓞 k) k (H0 p B O) := IsScalarTower.of_compHom _ _ _

theorem restr_injective [IsIntegral Y] (h : O' ≤ O) (hne : (O' : Set Y).Nonempty) :
    Function.Injective (restr h : H0 p B O → H0 p B O') := by
  refine (injective_iff_map_eq_zero _).2 fun f hf => LB.sec_ext fun i => fun_ext_ger fun y hy => ?_
  have : Nonempty (O' ⊓ B.U i : Y.Opens) := ((nonempty_preirreducible_inter O'.2 (B.U i).2 hne ⟨y, hy.2⟩)).to_subtype
  have e : resG Y (inf_le_inf_right _ h) (f.loc i) = resG Y (inf_le_inf_right _ h) 0 :=
    (congrArg (·.loc i) hf).trans (map_zero _).symm
  exact congrArg _ (map_injective_of_isIntegral Y (homOfLE (inf_le_inf_right _ h)) e)

theorem finite_top (hp : IsProjOver p) (hB : B.IsLB) : Module.Finite k (H0 p B ⊤) := by
  letI := algebraΓOfHom p
  letI : Module k B.Sec := Module.compHom _ (algebraMap k Γ(Y, ⊤))
  haveI : IsScalarTower k Γ(Y, ⊤) B.Sec := IsScalarTower.of_compHom _ _ _
  have e (c : k) : algebraMap k Γ(Y, ⊤) c = algX p ⊤ c := by
    change p.appTop _ = _
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have := finite_coh_zero_twist_of_isProjOver (fun _ => rfl) hp hB
  have := Module.Finite.equiv ((cohZeroTwistEquiv B).restrictScalars k)
  exact Module.Finite.of_surjective
    ({ H0.ofSec p ⊤ with map_smul' := fun c σ => (e c ▸ ofSec_smul c σ :) } : B.Sec →ₗ[k] H0 p B ⊤)
    bijective_ofSec_top.2

variable [Algebra k E] {q : T ⟶ Sp E} {r : T ⟶ Y} (H : IsPullback r q p (spMap (algebraMap k E)))
  {B' : LB T} (hB : B.IsLB) (hB' : B'.IsLB) (a : ChartPull B' B r) {W : T.Opens}


include hB hB' in
theorem linearIndependent_pullChart (h : W ≤ r ⁻¹ᵁ O) (h' : r ⁻¹ᵁ O ≤ W) {ι : Type*} [Fintype ι]
    {f : ι → H0 p B O} (hf : LinearIndependent k f) :
    LinearIndependent E fun i => pullChart a H.w h (f i) := by
  refine Fintype.linearIndependent_iff.2 fun u hu j => (Module.forall_dual_apply_eq_zero_iff k (u j)).1 fun l =>
    Fintype.linearIndependent_iff.1 hf (fun i => l (u i)) (ext_germ fun y hy => ?_) j
  obtain ⟨c, hc⟩ := exists_chart hB y
  obtain ⟨⟨V, hV⟩, hyV, hle⟩ := exists_affine (memInf hy hc)
  obtain ⟨Λ, hΛ⟩ := Adelic.IndepBaseChange.exists_contract (isPushout_sections p q r H V hV) l
  have e : ∑ i, algX q _ (u i) * (r.appLE V (r ⁻¹ᵁ V ⊓ q ⁻¹ᵁ ⊤) inf_le_left).hom (resG Y hle ((f i).loc c)) = 0 :=
    fun_ext_ger fun z hz => by
      obtain ⟨d, hd⟩ := exists_chart hB' z
      have hz' := hle hz.1
      have e := congrArg (germ d z (h' hz'.1) hd) hu

      simp only [map_sum, germ_smul, germ_pullChart, map_zero] at e

      simp only [map_sum, map_mul, ger_algX, ger_appLE, map_zero]
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) ((Finset.mul_sum _ _ _).symm.trans
        ((congrArg ((r.stalkMap z).hom (tr B (r z) c (a.idx d)).val * ·) e).trans (mul_zero _)))
      rw [mul_left_comm, ← map_mul]
      exact congrArg (_ * (r.stalkMap z).hom ·) ((ger_resG hle _ hz.1 _).trans
        (germ_change c _ _ hz'.1 hz'.2 (a.le d hd) (f i)))
  have e₂ := (map_sum Λ _ _).symm.trans ((congrArg Λ e).trans (map_zero Λ))
  have e₃ := congrArg (ger y hyV) ((Finset.sum_congr rfl fun i _ => (hΛ _ _).symm).trans e₂)
  refine ⟨c, hc, ?_⟩

  simp only [map_sum, map_mul, map_zero, ger_resG] at e₃

  simp only [map_sum, germ_smul, map_zero]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) e₃
  exact congrArg (· * _) (ger_algX y hyV _).symm


include hB hB' in
theorem isExtension_pullChart_top (hp : IsProjOver p) (hq : IsProjOver q) :
    IsExtension (pullChart (O := ⊤) (W := ⊤) a H.w le_top) := by
  refine ⟨fun _ _ => linearIndependent_pullChart H hB hB' a _ le_top, ?_⟩
  have := finite_top hp hB
  have := finite_top hq hB'
  have : IsProper p := by
    obtain ⟨N, i, hi, e⟩ := hp
    have := isProper_str k N
    rw [← e]
    infer_instance
  have e : Module.finrank E (H0 q B' ⊤) = Module.finrank k (H0 p B ⊤) := by
    letI := algebraΓOfHom q
    rw [H0.finrank_top, H0.finrank_top, lineBundleGlobalSectionsDim_congr_picardClass hB' (LB.isLB_pull hB r) ((cls_eq_iff _ _).2 (lbIso_of_chartPull
      ⟨fun i _ => a.idx i, fun i _ hz => mem_pull.2 (a.le i hz), fun z i j hi hj => (a.g z i j hi hj).trans ?_⟩
      (LB.isLB_pull hB r)))]
    · exact FieldChangeInter.hdim_pull H hB 0
    · exact ((GlobalTheory.chartPullPull B r).g z (fun _ => a.idx i) (fun _ => a.idx j) (mem_pull.2 (a.le i hi))
        (mem_pull.2 (a.le j hj))).symm
  refine top_le_iff.1 (((linearIndependent_pullChart (W := ⊤) H hB hB' a le_top le_top
    (Module.finBasis k (H0 p B ⊤)).linearIndependent).span_eq_top_of_card_eq_finrank'
      ((Fintype.card_fin _).trans e.symm)).ge.trans (Submodule.span_mono ?_))
  rintro _ ⟨i, rfl⟩
  exact ⟨_, rfl⟩

end Field

section General

variable {k k' : Type} [CommRing k] [CommRing k'] {p : Y ⟶ Sp k} {q : T ⟶ Sp k'} {φ : k →+* k'} {r : T ⟶ Y}
  {P B N : LB Y} {B' : LB T} {O O' : Y.Opens} {W W' : T.Opens}

theorem restr_pullChart (a : ChartPull B' B r) (hq : r ≫ p = q ≫ spMap φ) (h : W ≤ r ⁻¹ᵁ O) (h' : W' ≤ r ⁻¹ᵁ O')
    (e : O' ≤ O) (e' : W' ≤ W) (f : H0 p B O) :
    restr e' (pullChart a hq h f) = pullChart a hq h' (restr e f) :=
  LB.sec_ext fun i => fun_ext_ger fun z hz => by
    change germ i z hz.1 hz.2 _ = germ i z hz.1 hz.2 _
    rw [germ_restr, germ_pullChart, germ_pullChart]
    exact congrArg _ (germ_restr _ _ _ _ _ _).symm

def polarMap (C : ProdChart P B N) (t : P.Sec) (ht : O ≤ nonzeroLocus t) : H0 p N ⊤ →ₗ[k] H0 p B O :=
  (C.mulEquiv (σ := H0.ofSec p O t) fun y hy i hi => by
    rw [germ_ofSec, isUnit_ger_iff]; exact ht hy).symm.toLinearMap ∘ₗ restr le_top


variable (p B) in
def polar (hP : P.IsLB) (hB : B.IsLB) (t : P.Sec) (ht : O ≤ nonzeroLocus t) : Submodule k (H0 p B O) :=
  LinearMap.range (polarMap (tensChart hP hB) t ht)

variable (σ : k →+* ℂ)

def cval : H0 p B O →ₛₗ[σ] (B.ι → CxPts p σ → ℂ) where
  toFun f i := ev p σ (O ⊓ B.U i) (f.loc i)
  map_add' f g := funext₂ fun i y => ev_add _ _ y
  map_smul' c f := funext₂ fun i y => by
    refine (ev_mul _ _ y).trans ?_
    by_cases h : y ∈ ptsIn p σ (O ⊓ B.U i)
    · exact congrArg (· * _) ((ev_res inf_le_left h _).trans (ev_algX (ptsIn_mono inf_le_left h) c))
    · simp only [Pi.smul_apply, ev_of_notMem h, mul_zero, smul_zero]

theorem cval_ofSec (s : B.Sec) : cval σ (H0.ofSec p ⊤ s) = secVal p σ s := funext₂ fun i y => by
  by_cases h : y ∈ ptsIn p σ (B.U i)
  · exact ev_res inf_le_right (mem_ptsIn_inf.2 ⟨mem_ptsIn_top, h⟩) _
  · exact (ev_of_notMem (fun e => h (mem_ptsIn_inf.1 e).2) _).trans (ev_of_notMem h _).symm

theorem cval_mem (f : H0 p B ⊤) : cval σ f ∈ fibSec p σ B := by
  obtain ⟨s, rfl⟩ := bijective_ofSec_top.2 f
  exact cval_ofSec σ s ▸ secVal_mem s

variable {σ}

end General

end GlobalTheory.Vanishing
