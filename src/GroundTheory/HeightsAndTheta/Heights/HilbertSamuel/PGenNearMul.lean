module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenNearMul
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
import Mathlib.Order.Interval.Finset.Box

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GenNearMul

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
  {W : Ideal (MRingOver S ι)}

def act (hW : W ≤ Module.annihilator (MRingOver S ι) M) :
    (MRingOver S ι ⧸ W) →ₗ[MRingOver S ι] M →ₗ[MRingOver S ι] M :=
  Submodule.liftQ W (LinearMap.lsmul (MRingOver S ι) M) fun _ hr =>
    LinearMap.mem_ker.mpr (LinearMap.ext fun m => Module.mem_annihilator.mp (hW hr) m)

theorem act_mk (hW : W ≤ Module.annihilator (MRingOver S ι) M) (r : MRingOver S ι) (m : M) :
    act hW (Ideal.Quotient.mk W r) m = r • m := rfl

theorem act_smulS (hW : W ≤ Module.annihilator (MRingOver S ι) M) (c : S) (a : MRingOver S ι ⧸ W) (m : M) :
    act hW (c • a) m = c • act hW a m := by
  rw [LinearMap.map_smul_of_tower, LinearMap.smul_apply]

variable (T : Submonoid (MRingOver S ι))

def locMulFun (hW : W ≤ Module.annihilator (MRingOver S ι) M) (x : LocalizedModule T (MRingOver S ι ⧸ W))
    (y : LocalizedModule T M) : LocalizedModule T M :=
  x.liftOn (fun p => y.liftOn (fun q => LocalizedModule.mk (act hW p.1 q.1) (p.2 * q.2)) (by
      rintro ⟨m, t⟩ ⟨m', t'⟩ ⟨v, hv⟩
      refine LocalizedModule.mk_eq.mpr ⟨v, ?_⟩
      have h := congrArg (fun z => (p.2 : MRingOver S ι) • act hW p.1 z) hv
      simp only [Submonoid.smul_def, Submonoid.coe_mul, map_smul, smul_smul] at h ⊢
      convert h using 2 <;> ring)) (by
    rintro ⟨a, s⟩ ⟨a', s'⟩ ⟨u, hu⟩
    induction y with
    | h m t =>
      simp only [LocalizedModule.liftOn_mk]
      refine LocalizedModule.mk_eq.mpr ⟨u, ?_⟩
      have h := congrArg (fun b => (t : MRingOver S ι) • act hW b m) hu
      simp only [Submonoid.smul_def, Submonoid.coe_mul, map_smul, LinearMap.smul_apply, smul_smul] at h ⊢
      convert h using 2 <;> ring)

theorem locMulFun_mk (hW : W ≤ Module.annihilator (MRingOver S ι) M) (a : MRingOver S ι ⧸ W) (s : T) (m : M)
    (t : T) : locMulFun T hW (LocalizedModule.mk a s) (LocalizedModule.mk m t) =
      LocalizedModule.mk (act hW a m) (s * t) := by
  simp only [locMulFun, LocalizedModule.liftOn_mk]

def locMul (hW : W ≤ Module.annihilator (MRingOver S ι) M) :
    LocalizedModule T (MRingOver S ι ⧸ W) →ₗ[MRingOver S ι] LocalizedModule T M →ₗ[MRingOver S ι]
      LocalizedModule T M :=
  LinearMap.mk₂ (MRingOver S ι) (locMulFun T hW)
    (by
      intro x₁ x₂ y
      induction x₁ with | h a₁ s₁ =>
      induction x₂ with | h a₂ s₂ =>
      induction y with | h m t =>
      rw [LocalizedModule.mk_add_mk, locMulFun_mk, locMulFun_mk, locMulFun_mk, LocalizedModule.mk_add_mk]
      refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
      simp only [Submonoid.smul_def, Submonoid.coe_mul, one_smul, map_add (f := _), map_smul,
        LinearMap.add_apply, LinearMap.smul_apply, smul_add, smul_smul]
      module)
    (by
      intro c x y
      induction x with | h a s =>
      induction y with | h m t =>
      rw [LocalizedModule.smul'_mk, locMulFun_mk, locMulFun_mk, map_smul, LinearMap.smul_apply,
        LocalizedModule.smul'_mk])
    (by
      intro x y₁ y₂
      induction x with | h a s =>
      induction y₁ with | h m₁ t₁ =>
      induction y₂ with | h m₂ t₂ =>
      rw [LocalizedModule.mk_add_mk, locMulFun_mk, locMulFun_mk, locMulFun_mk, LocalizedModule.mk_add_mk]
      refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
      simp only [Submonoid.smul_def, Submonoid.coe_mul, one_smul, map_add (f := _), map_smul,
        smul_add, smul_smul]
      module)
    (by
      intro c x y
      induction x with | h a s =>
      induction y with | h m t =>
      rw [LocalizedModule.smul'_mk, locMulFun_mk, locMulFun_mk, map_smul, LocalizedModule.smul'_mk])

theorem locMul_mk (hW : W ≤ Module.annihilator (MRingOver S ι) M) (a : MRingOver S ι ⧸ W) (s : T) (m : M)
    (t : T) : locMul T hW (LocalizedModule.mk a s) (LocalizedModule.mk m t) =
      LocalizedModule.mk (act hW a m) (s * t) :=
  locMulFun_mk T hW a s m t

theorem locMul_smulS (hW : W ≤ Module.annihilator (MRingOver S ι) M) (c : S) (x y) :
    locMul T hW (c • x) y = c • locMul T hW x y ∧ locMul T hW x (c • y) = c • locMul T hW x y := by
  refine ⟨?_, LinearMap.map_smul_of_tower _ _ _⟩
  rw [LinearMap.map_smul_of_tower, LinearMap.smul_apply]

variable {T}

theorem cellRes_locMul (hW : W ≤ Module.annihilator (MRingOver S ι) M) {J I : ∀ k, Finset (ι k)}
    (x : LocalizedModule (KH.cellMon S J) (MRingOver S ι ⧸ W)) (y : LocalizedModule (KH.cellMon S J) M) :
    KH.cellRes S M J I (locMul _ hW x y) =
      locMul _ hW (KH.cellRes S (MRingOver S ι ⧸ W) J I x) (KH.cellRes S M J I y) := by
  by_cases h : KH.cellMon S J ≤ KH.cellMon S I
  · induction x with | h a s =>
    induction y with | h m t =>
    rw [locMul_mk, GenTwistGenerated.cellRes_mk h, GenTwistGenerated.cellRes_mk h,
      GenTwistGenerated.cellRes_mk h, locMul_mk]
    rfl
  · unfold KH.cellRes
    rw [dite_eq_right h]
    simp only [LinearMap.zero_apply, map_zero]

theorem act_mem (hW : W ≤ Module.annihilator (MRingOver S ι) M) {𝓜 : (K → ℤ) → Submodule S M}
    (h𝓜 : KH.IsMGraded S ι 𝓜) {c e : K → ℤ} {a : MRingOver S ι ⧸ W} (ha : a ∈ KH.quotPart S W c) {m : M}
    (hm : m ∈ 𝓜 e) : act hW a m ∈ 𝓜 (e + c) :=
  (Submodule.span_le.mpr (by
    rintro _ ⟨q, ⟨hc, hq⟩, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply,
      LinearMap.flip_apply, act_mk]
    convert h𝓜.2 _ e q m hq hm using 2
    funext k
    simp [hc k]) :
    KH.quotPart S W c ≤ (𝓜 (e + c)).comap (((act hW).flip m).restrictScalars S)) ha

theorem locMul_mem (hW : W ≤ Module.annihilator (MRingOver S ι) M) {𝓜 : (K → ℤ) → Submodule S M}
    (h𝓜 : KH.IsMGraded S ι 𝓜) {d n : K → ℤ} {T : Submonoid (MRingOver S ι)}
    {x : LocalizedModule T (MRingOver S ι ⧸ W)} {y : LocalizedModule T M}
    (hx : x ∈ KH.locPart ι (KH.quotPart S W) T n) (hy : y ∈ KH.locPart ι 𝓜 T d) :
    locMul T hW x y ∈ KH.locPart ι 𝓜 T (d + n) :=
  (Submodule.span_le.mpr (by
    rintro _ ⟨a, s, e, hs, ha, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply,
      LinearMap.flip_apply]
    refine (Submodule.span_le.mpr (by
      rintro _ ⟨m, t, e', ht, hm, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply, locMul_mk]
      refine Submodule.subset_span ⟨_, s * t, e + e',
        by simpa using GenTwistGenerated.isMultiHomog_mul hs ht, ?_, rfl⟩
      convert act_mem hW h𝓜 ha hm using 2
      funext k
      simp only [Pi.add_apply, Nat.cast_add]
      ring) :
      KH.locPart ι 𝓜 T d ≤
        (KH.locPart ι 𝓜 T (d + n)).comap ((locMul T hW _).restrictScalars S)) hy) :
    KH.locPart ι (KH.quotPart S W) T n ≤
      (KH.locPart ι 𝓜 T (d + n)).comap (((locMul T hW).flip y).restrictScalars S)) hx

theorem cechD_zero_apply_uniform (I : KH.Cell K ι 1) :
    ∃ J₁ J₂ : KH.Cell K ι 0, ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧
      ∀ (N : Type) [AddCommGroup N] [Module (MRingOver S ι) N] (f : KH.CechC S ι N 0),
        KH.cechD S ι N 0 f I = σ • (KH.cellRes S N J₁.1 I.1 (f J₁) - KH.cellRes S N J₂.1 I.1 (f J₂)) := by
  obtain ⟨J₁, J₂, -, -, σ, hσ, hd⟩ := GenTwistGenerated.cechD_zero_apply_uniform.{0} (S := S) I
  exact ⟨J₁, J₂, σ, hσ, hd⟩

def prodCochain (hW : W ≤ Module.annihilator (MRingOver S ι) M) (u : KH.CechC S ι (MRingOver S ι ⧸ W) 0)
    (z : KH.CechC S ι M 0) : KH.CechC S ι M 0 :=
  fun J => locMul (KH.cellMon S J.1) hW (u J) (z J)

theorem prodCochain_mem (hW : W ≤ Module.annihilator (MRingOver S ι) M) {𝓜 : (K → ℤ) → Submodule S M}
    (h𝓜 : KH.IsMGraded S ι 𝓜) {d n : K → ℤ} {u : KH.CechC S ι (MRingOver S ι ⧸ W) 0} {z : KH.CechC S ι M 0}
    (hu : u ∈ KH.cechZc ι (KH.quotPart S W) n 0) (hz : z ∈ KH.cechZc ι 𝓜 d 0) :
    prodCochain hW u z ∈ KH.cechZc ι 𝓜 (d + n) 0 := by
  refine ⟨Submodule.mem_pi.mpr fun J _ => locMul_mem hW h𝓜 (Submodule.mem_pi.mp hu.1 J (Set.mem_univ _))
    (Submodule.mem_pi.mp hz.1 J (Set.mem_univ _)), LinearMap.mem_ker.mpr ?_⟩
  funext I
  obtain ⟨J₁, J₂, σ, hσ, hd⟩ := cechD_zero_apply_uniform (S := S) I
  have hu' := GenTwistGenerated.res_eq_of_cechD hσ (hd _ u) (LinearMap.mem_ker.mp hu.2)
  have hz' := GenTwistGenerated.res_eq_of_cechD hσ (hd _ z) (LinearMap.mem_ker.mp hz.2)
  rw [hd]
  simp only [prodCochain, cellRes_locMul, hu', hz', sub_self]
  exact zsmul_zero σ

theorem isMultiHomog_pow {p : MRingOver S ι} {a : K → ℕ} (hp : IsMultiHomog p a) (m : ℕ) :
    IsMultiHomog (p ^ m) (m • a) := by
  induction m with
  | zero => simpa using GenTwistGenerated.isMultiHomog_one (S := S) (ι := ι) 0 fun _ => rfl
  | succ m ih =>
    rw [pow_succ, succ_nsmul]
    exact GenTwistGenerated.isMultiHomog_mul ih hp

def chartExpOf (c : ∀ k, ι k) (e : K → ℕ) : (Σ k, ι k) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun q => if q.2 = c q.1 then e q.1 else 0

def chartMon (c : ∀ k, ι k) (e : K → ℕ) : MRingOver S ι :=
  monomial (chartExpOf c e) 1

theorem chartMon_homog (c : ∀ k, ι k) (e : K → ℕ) : IsMultiHomog (chartMon (S := S) c e) e :=
  GenTwistGenerated.isMultiHomog_monomial _ _ _ fun k => by simp [chartExpOf]

theorem chartMon_mem {I : ∀ k, Finset (ι k)} {c : ∀ k, ι k} (hc : ∀ k, c k ∈ I k) (e : K → ℕ) :
    chartMon (S := S) c e ∈ KH.cellMon S I := by
  classical
  unfold chartMon
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul]
  refine Submonoid.prod_mem _ fun q hq => Submonoid.pow_mem _ (Submonoid.subset_closure ?_) _
  have hq' : q.2 = c q.1 := by
    by_contra h
    simp [chartExpOf, h] at hq
  obtain ⟨k, i⟩ := q
  simp only at hq'
  subst hq'
  exact ⟨k, c k, hc k, rfl⟩

theorem exists_div (hW : W ≤ Module.annihilator (MRingOver S ι) M) {𝓜 : (K → ℤ) → Submodule S M}
    (h𝓜 : KH.IsMGraded S ι 𝓜) {d n : K → ℤ} (I : ∀ k, Finset (ι k)) (P N : MRingOver S ι)
    (hP : P ∈ KH.cellMon S I) (hN : N ∈ KH.cellMon S I) (hPh : IsMultiHomog P fun k => (n k).toNat)
    (hNh : IsMultiHomog N fun k => (-n k).toNat) {x : LocalizedModule (KH.cellMon S I) M}
    (hx : x ∈ KH.locPart ι 𝓜 (KH.cellMon S I) (d + n)) :
    ∃ y ∈ KH.locPart ι 𝓜 (KH.cellMon S I) d,
      locMul _ hW (LocalizedModule.mk (Ideal.Quotient.mk W P) ⟨N, hN⟩) y = x :=
  (Submodule.span_le.mpr (by
    rintro _ ⟨m, s, e, hs, hm, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_map]
    refine ⟨LocalizedModule.mk (N • m) (⟨P, hP⟩ * s),
      Submodule.subset_span ⟨N • m, ⟨P, hP⟩ * s, (fun k => (n k).toNat) + e,
        by simpa using GenTwistGenerated.isMultiHomog_mul hPh hs, ?_, rfl⟩, ?_⟩
    · convert h𝓜.2 _ _ N m hNh hm using 2
      funext k
      have := Int.toNat_sub_toNat_neg (n k)
      simp only [Pi.add_apply, Nat.cast_add]
      omega
    · rw [LinearMap.restrictScalars_apply, locMul_mk, act_mk]
      refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
      simp only [Submonoid.smul_def, Submonoid.coe_mul, one_smul, smul_smul]
      congr 1
      ring) :
    KH.locPart ι 𝓜 (KH.cellMon S I) (d + n) ≤ (KH.locPart ι 𝓜 (KH.cellMon S I) d).map
      ((locMul _ hW (LocalizedModule.mk (Ideal.Quotient.mk W P) ⟨N, hN⟩)).restrictScalars S)) hx

end GenNearMul

theorem GenNearMul.proof : GenNearMul.Statement := by
  intro S _ K _ _ ι _ _ M _ _ _ _ 𝓜 W d n f g δ γ h𝓜 hW hf hg hM hO I x hx
  classical
  let c : ∀ k, ι k := fun k => (I.2.1 k).choose
  have hc : ∀ k, c k ∈ I.1 k := fun k => (I.2.1 k).choose_spec
  have hP := GenNearMul.chartMon_mem (S := S) hc fun k => (n k).toNat
  have hN := GenNearMul.chartMon_mem (S := S) hc fun k => (-n k).toNat
  obtain ⟨y, hy, hxy⟩ := GenNearMul.exists_div hW h𝓜 I.1 _ _ hP hN (GenNearMul.chartMon_homog _ _)
    (GenNearMul.chartMon_homog _ _) hx
  have hn : ∀ k, n k + ((-n k).toNat : ℤ) = ((n k).toNat : ℤ) := fun k => by
    have := Int.toNat_sub_toNat_neg (n k)
    omega
  have hw : LocalizedModule.mk (Ideal.Quotient.mk W (GenNearMul.chartMon (S := S) c fun k => (n k).toNat))
      (⟨_, hN⟩ : KH.cellMon S I.1) ∈ KH.locPart ι (KH.quotPart S W) (KH.cellMon S I.1) n := by
    refine Submodule.subset_span ⟨_, ⟨_, hN⟩, fun k => (-n k).toNat, GenNearMul.chartMon_homog _ _,
      Submodule.subset_span ⟨_, ⟨fun k => ?_, ?_⟩, rfl⟩, rfl⟩
    · rw [Pi.add_apply, hn k]
      exact Int.natCast_nonneg _
    · convert GenNearMul.chartMon_homog (S := S) c (fun k => (n k).toNat) using 2
      simp only [Pi.add_apply, hn, Int.toNat_natCast]
  obtain ⟨a, t, e, r, p, z, ht, hth, hp, hz, hyz⟩ := hM I y hy
  obtain ⟨b, t', e', r', q, u, ht', ht'h, hq, hu, hwu⟩ := hO I _ hw
  refine ⟨a + b, t * t', e + e', r * r',
    fun i => f ^ b * g ^ a * p (finProdFinEquiv.symm i).1 * q (finProdFinEquiv.symm i).2,
    fun i => GenNearMul.prodCochain hW (u (finProdFinEquiv.symm i).2) (z (finProdFinEquiv.symm i).1),
    mul_mem ht ht', GenTwistGenerated.isMultiHomog_mul hth ht'h, fun i => ?_,
    fun i => GenNearMul.prodCochain_mem hW h𝓜 (hu _) (hz _), ?_⟩
  · have h1 := GenTwistGenerated.isMultiHomog_mul (GenTwistGenerated.isMultiHomog_mul
      (GenTwistGenerated.isMultiHomog_mul (GenNearMul.isMultiHomog_pow hf b) (GenNearMul.isMultiHomog_pow hg a))
      (hp (finProdFinEquiv.symm i).1)) (hq (finProdFinEquiv.symm i).2)
    convert h1 using 1
    ring
  · rw [← hxy]
    have key : ((f * g) ^ (a + b) * (t * t')) • GenNearMul.locMul _ hW
          (LocalizedModule.mk (Ideal.Quotient.mk W (GenNearMul.chartMon (S := S) c fun k => (n k).toNat))
            (⟨_, hN⟩ : KH.cellMon S I.1)) y =
        (f ^ b * g ^ a) • GenNearMul.locMul _ hW ((g ^ b * t') •
          LocalizedModule.mk (Ideal.Quotient.mk W (GenNearMul.chartMon (S := S) c fun k => (n k).toNat))
            (⟨_, hN⟩ : KH.cellMon S I.1)) ((f ^ a * t) • y) := by
      simp only [map_smul, LinearMap.smul_apply, smul_smul]
      congr 1
      ring
    rw [key, hwu, hyz]

    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
    rw [← Equiv.sum_comp finProdFinEquiv]
    simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, GenNearMul.prodCochain]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_assoc (f ^ b * g ^ a)]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
