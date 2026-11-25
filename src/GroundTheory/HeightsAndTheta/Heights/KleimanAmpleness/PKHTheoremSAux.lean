module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgCechSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgFiltSt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGradedSubquot
public import Mathlib.Algebra.Order.PUnit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AmpleSt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CechHcSubsingletonOfBij
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.H1VanishGeneratedOfLocalizedSubsingleton
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenSESStep
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGradedSubquot
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PQuotPartGraded
import Mathlib.Topology.Sheaves.Presheaf
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKleimanScheme

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace KHTheoremS

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

theorem cechHc_subsingleton_of_cochains {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (c : K → ℤ) (n : ℕ)
    (h : Subsingleton (KH.CechC S ι M n)) : Subsingleton (KH.cechHc ι 𝓜 c n) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Subtype.ext (Subsingleton.elim (x : KH.CechC S ι M n) y)]

theorem cechHc_punit (c : K → ℤ) (n : ℕ) :
    Subsingleton (KH.cechHc ι (fun _ : K → ℤ => (⊥ : Submodule S PUnit)) c n) :=
  cechHc_subsingleton_of_cochains _ c n
    ⟨fun _ _ => funext fun _ => Subsingleton.elim (α := LocalizedModule _ PUnit) _ _⟩

theorem exists_mem_of_surjective {M M'' : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] [AddCommGroup M''] [Module (MRingOver S ι) M''] [Module S M'']
    [IsScalarTower S (MRingOver S ι) M''] {𝓜 : (K → ℤ) → Submodule S M} {𝓜'' : (K → ℤ) → Submodule S M''}
    (h𝓜 : KH.IsMGraded S ι 𝓜) (h𝓜'' : KH.IsMGraded S ι 𝓜'') {h : M →ₗ[MRingOver S ι] M''}
    (hh : KH.IsMGradedMap S ι 𝓜 𝓜'' h) (hs : Function.Surjective h) {c : K → ℤ} {m'' : M''}
    (hm : m'' ∈ 𝓜'' c) : ∃ m ∈ 𝓜 c, h m = m'' := by
  obtain ⟨x, rfl⟩ := hs m''
  obtain ⟨d, hd⟩ := h𝓜.1.2 x
  let f : ∀ j, 𝓜 j →+ 𝓜'' j := fun j =>
    { toFun := fun a => ⟨h a.1, hh j a.1 a.2⟩,
      map_zero' := Subtype.ext (map_zero h),
      map_add' := fun a b => Subtype.ext (map_add h a.1 b.1) }
  have hcomm : h.toAddMonoidHom.comp (DirectSum.coeAddMonoidHom 𝓜) =
      (DirectSum.coeAddMonoidHom 𝓜'').comp (DirectSum.map f) :=
    DirectSum.addHom_ext fun j a => by
      simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of, DirectSum.map_of]; rfl
  have heq : DirectSum.map f d = DirectSum.of (fun j => 𝓜'' j) c ⟨h x, hm⟩ := h𝓜''.1.1 <| by
    have h1 := DFunLike.congr_fun hcomm d
    simp only [AddMonoidHom.comp_apply, hd] at h1
    rw [← h1, DirectSum.coeAddMonoidHom_of]
    rfl
  have hc := congrArg (fun z => (z c : M'')) heq
  simp only [DirectSum.map_apply, DirectSum.of_eq_same] at hc
  exact ⟨(d c : M), (d c).2, hc⟩

abbrev lmap {M N : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [AddCommGroup N] [Module (MRingOver S ι) N]
    (T : Submonoid (MRingOver S ι)) (g : M →ₗ[MRingOver S ι] N) :
    LocalizedModule T M →ₗ[MRingOver S ι] LocalizedModule T N :=
  IsLocalizedModule.map T (LocalizedModule.mkLinearMap T M) (LocalizedModule.mkLinearMap T N) g

theorem lmap_mk {M N : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [AddCommGroup N]
    [Module (MRingOver S ι) N] {T : Submonoid (MRingOver S ι)} (g : M →ₗ[MRingOver S ι] N) (m : M) (t : T) :
    lmap T g (LocalizedModule.mk m t) = LocalizedModule.mk (g m) t := by
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.map_mk', ← IsLocalizedModule.mk_eq_mk']

theorem cechMap_apply {M N : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [AddCommGroup N]
    [Module (MRingOver S ι) N] (g : M →ₗ[MRingOver S ι] N) (n : ℕ) (z : KH.CechC S ι M n) (I : KH.Cell K ι n) :
    KH.cechMap S ι g n z I = lmap (KH.cellMon S I.1) g (z I) := rfl

theorem cellRes_locMap {M N : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [AddCommGroup N]
    [Module (MRingOver S ι) N] (g : M →ₗ[MRingOver S ι] N) (J I : ∀ k, Finset (ι k))
    (x : LocalizedModule (KH.cellMon S J) M) :
    KH.cellRes S N J I (lmap (KH.cellMon S J) g x) =
      lmap (KH.cellMon S I) g (KH.cellRes S M J I x) := by
  by_cases h : KH.cellMon S J ≤ KH.cellMon S I
  · induction x using LocalizedModule.induction_on with
    | h m t =>
      rw [lmap_mk, GenTwistGenerated.cellRes_mk h, GenTwistGenerated.cellRes_mk h,
        lmap_mk]
  · unfold KH.cellRes
    rw [dite_eq_right h, dite_eq_right h, LinearMap.zero_apply, LinearMap.zero_apply, map_zero]

theorem cechD_cechMap {M N : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [AddCommGroup N]
    [Module (MRingOver S ι) N] (g : M →ₗ[MRingOver S ι] N) (n : ℕ) (z : KH.CechC S ι M n) :
    KH.cechD S ι N n (KH.cechMap S ι g n z) = KH.cechMap S ι g (n + 1) (KH.cechD S ι M n z) := by
  funext I
  rw [cechMap_apply]

  simp only [KH.cechD, LinearMap.pi_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hI
  · change KH.faceSign I.1 k i • KH.cellRes S N _ I.1 (KH.cechMap S ι g n z ⟨_, hI⟩) =
      lmap (KH.cellMon S I.1) g (KH.faceSign I.1 k i • KH.cellRes S M _ I.1 (z ⟨_, hI⟩))
    exact (congrArg (KH.faceSign I.1 k i • ·) (cellRes_locMap g (Function.update I.1 k ((I.1 k).erase i)) I.1
      (z ⟨_, hI⟩))).trans (map_zsmul (lmap (KH.cellMon S I.1) g) _ _).symm
  · simp only [LinearMap.zero_apply, map_zero]

theorem locMap_mem_locPart {M N : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] [AddCommGroup N] [Module (MRingOver S ι) N] [Module S N]
    [IsScalarTower S (MRingOver S ι) N] {𝓜 : (K → ℤ) → Submodule S M} {𝓝 : (K → ℤ) → Submodule S N}
    {g : M →ₗ[MRingOver S ι] N} (hg : KH.IsMGradedMap S ι 𝓜 𝓝 g) {T : Submonoid (MRingOver S ι)} {c : K → ℤ}
    {x : LocalizedModule T M} (hx : x ∈ KH.locPart ι 𝓜 T c) : lmap T g x ∈ KH.locPart ι 𝓝 T c := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    rw [lmap_mk]
    exact GenSESStep.mk_mem_locPart _ t a ht (hg _ m hm)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul s x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ s hx

theorem cechMap_mem_cechZc {M N : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] [AddCommGroup N] [Module (MRingOver S ι) N] [Module S N]
    [IsScalarTower S (MRingOver S ι) N] {𝓜 : (K → ℤ) → Submodule S M} {𝓝 : (K → ℤ) → Submodule S N}
    {g : M →ₗ[MRingOver S ι] N} (hg : KH.IsMGradedMap S ι 𝓜 𝓝 g) {c : K → ℤ} {n : ℕ} {z : KH.CechC S ι M n}
    (hz : z ∈ KH.cechZc ι 𝓜 c n) : KH.cechMap S ι g n z ∈ KH.cechZc ι 𝓝 c n := by
  obtain ⟨h1, h2⟩ := hz
  refine ⟨Submodule.mem_pi.mpr fun I _ => ?_, LinearMap.mem_ker.mpr ?_⟩
  · rw [cechMap_apply]
    exact locMap_mem_locPart hg (Submodule.mem_pi.mp h1 I (Set.mem_univ _))
  · rw [cechD_cechMap, LinearMap.mem_ker.mp h2, map_zero]

theorem const_mem_cechZc {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M} {c : K → ℤ} {m : M} (hm : m ∈ 𝓜 c) :
    (fun _ => LocalizedModule.mk m 1 : KH.CechC S ι M 0) ∈ KH.cechZc ι 𝓜 c 0 := by
  refine ⟨Submodule.mem_pi.mpr fun I _ => ?_, LinearMap.mem_ker.mpr ?_⟩
  · have e : (c + fun k => (((0 : K → ℕ) k : ℕ) : ℤ)) = c := by
      funext k
      simp
    exact GenSESStep.mk_mem_locPart (c := c) m 1 0 isMultiHomog_one_zero (by rw [e]; exact hm)
  · funext I
    obtain ⟨J₁, J₂, h₁, h₂, σ, -, hd⟩ := GenTwistGenerated.cechD_zero_apply (S := S) (M := M) I
    rw [hd, GenTwistGenerated.cellRes_mk (GenTwistGenerated.cellMon_mono h₁),
      GenTwistGenerated.cellRes_mk (GenTwistGenerated.cellMon_mono h₂)]
    exact (congrArg (σ • ·) (sub_self _)).trans (zsmul_zero σ)

theorem devissage (hPF : KH.PrimeFiltStatement) (hS : IsNoetherianRing S)
    (C : ∀ (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
      [IsScalarTower S (MRingOver S ι) M], ((K → ℤ) → Submodule S M) → Prop)
    (h0 : C PUnit (fun _ => ⊥))
    (hext : ∀ (M' : Type) [AddCommGroup M'] [Module (MRingOver S ι) M'] [Module S M']
      [IsScalarTower S (MRingOver S ι) M'] (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
      [IsScalarTower S (MRingOver S ι) M] (M'' : Type) [AddCommGroup M''] [Module (MRingOver S ι) M'']
      [Module S M''] [IsScalarTower S (MRingOver S ι) M'']
      (𝓜' : (K → ℤ) → Submodule S M') (𝓜 : (K → ℤ) → Submodule S M) (𝓜'' : (K → ℤ) → Submodule S M'')
      (g : M' →ₗ[MRingOver S ι] M) (h : M →ₗ[MRingOver S ι] M''),
      KH.IsMGraded S ι 𝓜' → KH.IsMGraded S ι 𝓜 → KH.IsMGraded S ι 𝓜'' →
      KH.IsMGradedMap S ι 𝓜' 𝓜 g → KH.IsMGradedMap S ι 𝓜 𝓜'' h →
      Function.Injective g → Function.Surjective h → LinearMap.range g = LinearMap.ker h →
      C M' 𝓜' → C M'' 𝓜'' → C M 𝓜)
    (hq : ∀ 𝔭 : Ideal (MRingOver S ι), 𝔭.IsPrime → IsMultiHomogIdeal 𝔭 → ∀ e : K → ℤ,
      C (MRingOver S ι ⧸ 𝔭) (fun d => KH.quotPart S 𝔭 (d + e)))
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (hfin : Module.Finite (MRingOver S ι) M) (hgr : KH.IsMGraded S ι 𝓜) :
    C M 𝓜 :=
  H1VanishingDevissage.devissage hPF GradedSubquot.proof hS C h0 hext M 𝓜 hfin hgr
    fun 𝔭 hp hmh _ e => hq 𝔭 hp hmh e

def idealSub (V : Ideal (MRingOver S ι)) :
    Submodule (MRingOver S ι) (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) :=
  Submodule.map (Submodule.mkQ ⊥) V

def quotMap (V : Ideal (MRingOver S ι)) :
    (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) →ₗ[MRingOver S ι] MRingOver S ι ⧸ V :=
  Submodule.liftQ ⊥ (Submodule.mkQ V) (by simp)

theorem bot_isMultiHomogIdeal : IsMultiHomogIdeal (⊥ : Ideal (MRingOver S ι)) :=
  ⟨∅, fun _ h => absurd h (Set.notMem_empty _), by simp⟩

theorem quotSES (V : Ideal (MRingOver S ι)) (hV : IsMultiHomogIdeal V) (e : K → ℤ) :
    KH.IsMGraded S ι (subGrading (fun d => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (d + e)) (idealSub V)) ∧
    KH.IsMGraded S ι (fun d => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (d + e)) ∧
    KH.IsMGraded S ι (fun d => KH.quotPart S V (d + e)) ∧
    KH.IsMGradedMap S ι (subGrading (fun d => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (d + e)) (idealSub V))
      (fun d => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (d + e)) (idealSub V).subtype ∧
    KH.IsMGradedMap S ι (fun d => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (d + e))
      (fun d => KH.quotPart S V (d + e)) (quotMap V) ∧
    Function.Injective (idealSub V).subtype ∧ Function.Surjective (quotMap V) ∧
    LinearMap.range (idealSub V).subtype = LinearMap.ker (quotMap V) := by
  have hF := H1VanishingDevissage.isMGraded_shift (QuotPartGraded.proof S K ι ⊥ bot_isMultiHomogIdeal) e
  refine ⟨?_, hF, H1VanishingDevissage.isMGraded_shift (QuotPartGraded.proof S K ι V hV) e, fun _ _ hx => hx,
    ?_, Submodule.injective_subtype _, ?_, ?_⟩
  · obtain ⟨T, hT, rfl⟩ := hV
    have hN : idealSub (Ideal.span T) =
        Submodule.span (MRingOver S ι) (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) '' T) := by
      rw [idealSub, Ideal.span, Submodule.map_span]
      rfl
    have hH : ∀ x ∈ Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) '' T,
        ∃ c', x ∈ KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c' + e) := by
      rintro _ ⟨f, hf, rfl⟩
      obtain ⟨a, ha⟩ := hT f hf
      refine ⟨(fun k => (a k : ℤ)) - e, ?_⟩
      rw [sub_add_cancel]
      refine Submodule.subset_span ⟨f, ⟨fun k => Int.natCast_nonneg _, ?_⟩, rfl⟩
      have : (fun k => ((a k : ℤ)).toNat) = a := funext fun k => Int.toNat_natCast _
      rw [this]
      exact ha
    rw [hN]
    exact (GradedSubquot.proof S K ι _ _ _ _ hF hH hH le_rfl).1
  · intro d x hx
    refine (Submodule.span_le (p := (KH.quotPart S V (d + e)).comap ((quotMap V).restrictScalars S))).2 ?_ hx
    rintro _ ⟨p, hp, rfl⟩
    exact Submodule.subset_span ⟨p, hp, rfl⟩
  · intro y
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective V y
    exact ⟨Submodule.Quotient.mk p, rfl⟩
  · rw [Submodule.range_subtype, quotMap, Submodule.ker_liftQ, Submodule.ker_mkQ, idealSub]

theorem idealSub_finite (hS : IsNoetherianRing S) (V : Ideal (MRingOver S ι)) :
    Module.Finite (MRingOver S ι) (idealSub V) := by
  have : IsNoetherianRing (MRingOver S ι) := inferInstance
  have : IsNoetherian (MRingOver S ι) (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) := inferInstance
  exact Module.IsNoetherian.finite _ _

end KHTheoremS

theorem KHCechTop.full : KH.CechTopStatement := by
  intro S _ K _ _ ι _ _ M _ _ _ _ 𝓜 c n hn
  refine KHTheoremS.cechHc_subsingleton_of_cochains 𝓜 c n ⟨fun _ _ => funext fun I => ?_⟩
  exfalso
  have hle : ∑ k, ((I.1 k).card - 1) ≤ ∑ k, (Fintype.card (ι k) - 1) :=
    Finset.sum_le_sum fun k _ => Nat.sub_le_sub_right (Finset.card_le_univ _) 1
  rw [I.2.2] at hle
  omega

end

end GroundTheory.Heights₂.Heights.Kleiman
