module

import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IdealsOfNormEqIndexSet
public import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

@[expose] public section

namespace Formalism.HermitianLatticeCounting.P

section homRestrict
open Module

lemma s5b7_card_comp {R A B C : Type*} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hg : Function.Injective g) :
    Nat.card (C ⧸ LinearMap.range (g ∘ₗ f)) =
      Nat.card (B ⧸ LinearMap.range f) * Nat.card (C ⧸ LinearMap.range g) := by
  rw [← Submodule.card_quotient_mul_card_quotient (LinearMap.range g) _
    (LinearMap.range_comp f g ▸ LinearMap.map_le_range)]; congr 1
  let h := (LinearMap.range (g ∘ₗ f)).mkQ ∘ₗ g
  have hker : LinearMap.ker h = LinearMap.range f := by ext x; simp [h, hg.eq_iff]
  exact Nat.card_congr (((Submodule.quotEquivOfEq _ _ hker.symm).trans h.quotKerEquivRange).trans
    (LinearEquiv.ofEq _ _ (LinearMap.range_comp _ _))).symm.toEquiv

variable {O : Type} [CommRing O] [IsDedekindDomain O]

lemma s5b7_proj (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y]
    [Module.IsTorsionFree O Y] : Module.Projective O Y :=
  have := Module.finitePresentation_of_finite O Y; Module.Flat.projective_of_finitePresentation

lemma s5b7_quot_ge (p : Ideal O) [hp : p.IsMaximal] [Finite (O ⧸ p)] (Y : Type) [AddCommGroup Y]
    [Module O Y] [Module.Finite O Y] [Module.IsTorsionFree O Y] :
    Finite (Y ⧸ p • (⊤ : Submodule O Y)) ∧
    Nat.card (O ⧸ p) ^ finrank O Y ≤ Nat.card (Y ⧸ p • (⊤ : Submodule O Y)) := by
  classical
  set P := p • (⊤ : Submodule O Y); let : Field (O ⧸ p) := Ideal.Quotient.field p
  have : Module.Finite (O ⧸ p) (Y ⧸ P) := .of_restrictScalars_finite O _ _
  refine ⟨Module.finite_of_finite (O ⧸ p), ?_⟩
  rw [Module.natCard_eq_pow_finrank (K := O ⧸ p) (V := Y ⧸ P)]
  apply Nat.pow_le_pow_right Nat.card_pos
  let b := Module.finBasis (O ⧸ p) (Y ⧸ P)
  choose y hy using fun i => Submodule.Quotient.mk_surjective P (b i)
  set N := Submodule.span O (Set.range y)
  have hsup : P ⊔ N = ⊤ := by
    simpa [Submodule.ker_mkQ] using congrArg (Submodule.comap P.mkQ) (show N.map P.mkQ = ⊤ by
      rw [Submodule.map_span, ← Set.range_comp, show P.mkQ ∘ y = b from funext hy,
        ← Submodule.restrictScalars_span O (O ⧸ p) Ideal.Quotient.mk_surjective, b.span_eq]; rfl)
  have htop : (⊤ : Submodule O (Y ⧸ N)) ≤ p • ⊤ :=
    calc (⊤ : Submodule O (Y ⧸ N))
        = (P ⊔ N).map N.mkQ := by rw [hsup, Submodule.map_top, N.range_mkQ]
      _ = P.map N.mkQ := by rw [Submodule.map_sup, N.mkQ_map_self, sup_bot_eq]
      _ ≤ p • ⊤ := Submodule.map_smul'' p ⊤ N.mkQ ▸ Submodule.smul_mono le_rfl le_top
  obtain ⟨s, hs1, hs⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul p _
    Module.Finite.fg_top htop
  have : IsNoetherian O Y := isNoetherian_of_isNoetherianRing_of_finite O Y
  refine (LinearMap.finrank_le_finrank_of_injective
    (f := (LinearMap.lsmul O Y s).codRestrict N fun z =>
      (Submodule.Quotient.mk_eq_zero N).mp (by simpa using hs (Submodule.Quotient.mk z) trivial))
    fun _ _ h => smul_right_injective Y
      (fun h0 => hp.ne_top ((Ideal.eq_top_iff_one p).mpr (by simpa [h0] using p.neg_mem hs1)))
      (congrArg Subtype.val h)).trans ((finrank_range_le_card y).trans_eq (Fintype.card_fin _))

theorem s5b7_quot (p : Ideal O) [hp : p.IsMaximal] [Finite (O ⧸ p)] (Y : Type) [AddCommGroup Y]
    [Module O Y] [Module.Finite O Y] [Module.Projective O Y] :
    Nat.card (Y ⧸ p • (⊤ : Submodule O Y)) = Nat.card (O ⧸ p) ^ finrank O Y := by
  classical
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' O Y
  obtain ⟨h, hh⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hfh (x) : f (h x) = x := by simpa using LinearMap.congr_fun hh x
  set Q := LinearMap.ker f
  have : IsNoetherian O (Fin n → O) := isNoetherian_of_isNoetherianRing_of_finite _ _
  let e : (Fin n → O) ≃ₗ[O] Y × Q := LinearEquiv.ofLinearMap
    (f.prod ((LinearMap.id - h ∘ₗ f).codRestrict Q fun x => by simp [Q, hfh])) (h.coprod Q.subtype)
    (by ext x <;> simp [hfh, show ∀ q : Q, f q = 0 from fun q => q.2]) (by ext x; simp)
  have hrank : finrank O Y + finrank O Q = n := by
    have := Submodule.finrank_quotient_add_finrank Q
    rwa [(LinearMap.quotKerEquivOfSurjective f hf).finrank_eq, Module.finrank_fin_fun] at this
  have hprod : (p • (⊤ : Submodule O Y)).toAddSubgroup.index *
      (p • (⊤ : Submodule O Q)).toAddSubgroup.index =
      Nat.card (O ⧸ p) ^ finrank O Y * Nat.card (O ⧸ p) ^ finrank O Q := by
    calc _ = (p • (⊤ : Submodule O (Y × Q))).toAddSubgroup.index := by
            rw [Formalism.HermitianLatticeCounting.P.ideal_smul_top_prod, ← AddSubgroup.index_prod]; rfl
      _ = (p • (⊤ : Submodule O (Fin n → O))).toAddSubgroup.index :=
            (Nat.card_congr (Submodule.Quotient.equiv _ _ e
              (by rw [Submodule.map_smul'', Submodule.map_top, e.range])).toEquiv).symm
      _ = (AddSubgroup.pi Set.univ fun _ : Fin n => p.toAddSubgroup).index := by
            congr 1; ext x; simp only [Submodule.mem_toAddSubgroup, Formalism.HermitianLatticeCounting.P.mem_ideal_smul_top_pi_iff,
              AddSubgroup.mem_pi, Set.mem_univ, forall_true_left]
      _ = _ := by
            rw [AddSubgroup.index_pi, ← pow_add, hrank]
            simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]; rfl
  by_contra hne; exact absurd hprod (ne_of_gt ((Nat.mul_lt_mul_of_pos_right
    (lt_of_le_of_ne (s5b7_quot_ge p Y).2 (Ne.symm hne)) (pow_pos Nat.card_pos _)).trans_le
    (Nat.mul_le_mul_left _ (s5b7_quot_ge p Q).2)))

theorem s5b7_ideal (p : Ideal O) [hp : p.IsMaximal] (hp0 : p ≠ ⊥) [Finite (O ⧸ p)] (X : Type)
    [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] :
    Nat.card ((p →ₗ[O] X) ⧸ LinearMap.range (LinearMap.lcomp O X (Submodule.subtype p))) =
      Nat.card (O ⧸ p) ^ finrank O X := by
  classical
  have : Module.Projective O p := s5b7_proj p
  have : Module.Projective O (p →ₗ[O] X) := s5b7_proj _
  obtain ⟨t, htp, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp0
  have hcomm (ψ : p →ₗ[O] X) (a c : p) : (a : O) • ψ c = (c : O) • ψ a := by
    rw [← map_smul, ← map_smul]; congr 1; ext; exact mul_comm _ _
  have hrange : LinearMap.range (LinearMap.lcomp O X p.subtype) = p • ⊤ := by
    refine le_antisymm ?_ (Submodule.smul_le.mpr fun a ha ψ _ =>
      ⟨LinearMap.toSpanSingleton O X (ψ ⟨a, ha⟩),
        LinearMap.ext fun c => by simpa using hcomm ψ c ⟨a, ha⟩⟩)
    rintro _ ⟨ψ, rfl⟩; obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' O p
    obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id hg
    have key : LinearMap.lcomp O X p.subtype ψ =
        ∑ i, ((g (fun j => if i = j then 1 else 0) : p) : O) • (ψ ∘ₗ LinearMap.proj i ∘ₗ s) := by
      ext c; simp only [LinearMap.lcomp_apply, Submodule.subtype_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, ← map_smul, ← map_sum]
      congr 1; conv_lhs =>
        rw [← show g (s c) = c by simpa using LinearMap.congr_fun hs c, pi_eq_sum_univ (s c)]
      simp [map_sum, mul_comm]
    exact key ▸ Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (g _).2 trivial
  rw [hrange, s5b7_quot p (p →ₗ[O] X)]; congr 1; refine le_antisymm
    (LinearMap.finrank_le_finrank_of_injective (f := LinearMap.applyₗ (⟨t, htp⟩ : p)) ?_)
    (LinearMap.finrank_le_finrank_of_injective (f := LinearMap.lcomp O X p.subtype ∘ₗ
      (LinearMap.ringLmapEquivSelf O O X).symm.toLinearMap) ?_)
  · exact fun ψ₁ ψ₂ h => LinearMap.ext fun c => smul_right_injective X ht0 (by
      change ((⟨t, htp⟩ : p) : O) • ψ₁ c = ((⟨t, htp⟩ : p) : O) • ψ₂ c
      rw [hcomm ψ₁ ⟨t, htp⟩ c, hcomm ψ₂ ⟨t, htp⟩ c]; exact congrArg ((c : O) • ·) h)
  · exact fun x₁ x₂ h => smul_right_injective X ht0 (by simpa using LinearMap.congr_fun h ⟨t, htp⟩)

theorem s5b7_step (hO : ¬ IsField O) (M X : Type) [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [AddCommGroup X] [Module O X] [Module.Finite O X]
    [Module.Projective O X] (N : Submodule O M) (hN : IsCoatom N) [Finite (M ⧸ N)] :
    Nat.card ((N →ₗ[O] X) ⧸ LinearMap.range (LinearMap.lcomp O X N.subtype)) =
      Nat.card (M ⧸ N) ^ finrank O X := by
  classical
  obtain ⟨p, hp, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp (isSimpleModule_iff_isCoatom.mpr hN)
  have hp0 : p ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp hO
  have : Finite (O ⧸ p) := Finite.of_equiv _ e.toEquiv
  let π : M →ₗ[O] O ⧸ p := e.toLinearMap ∘ₗ N.mkQ
  have hπN (m) : π m = 0 ↔ m ∈ N := by simp [π]
  obtain ⟨l, hl⟩ := Module.projective_lifting_property p.mkQ π (Submodule.mkQ_surjective p)
  have hl' (m) : p.mkQ (l m) = π m := LinearMap.congr_fun hl m
  obtain ⟨x, hx⟩ : ∃ x, π x = p.mkQ 1 := (e.surjective.comp (Submodule.mkQ_surjective N)) _
  have hlp (m) : l m ∈ p ↔ m ∈ N := by
    rw [← hπN, ← hl', Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hax (a : O) : π (a • x) = p.mkQ a := by rw [map_smul, hx, ← map_smul, smul_eq_mul, mul_one]
  let sx := LinearMap.toSpanSingleton O M x
  let j : p →ₗ[O] N := (sx ∘ₗ p.subtype).codRestrict N fun a => (hπN _).mp (by
    change π ((a : O) • x) = 0; rw [hax, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact a.2)
  let R := LinearMap.range (LinearMap.lcomp O X p.subtype)
  let Θ : (N →ₗ[O] X) →ₗ[O] (p →ₗ[O] X) ⧸ R := R.mkQ ∘ₗ LinearMap.lcomp O X j
  have hker : LinearMap.ker Θ = LinearMap.range (LinearMap.lcomp O X N.subtype) := by
    ext φ; simp only [Θ, R, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
    refine ⟨fun ⟨ψ, hψ⟩ => ?_, fun ⟨Φ, hΦ⟩ =>
      ⟨LinearMap.toSpanSingleton O X (Φ x), by ext a; simp [← hΦ, j, sx]⟩⟩
    let ρ : M →ₗ[O] N := (LinearMap.id - sx ∘ₗ l).codRestrict N fun m =>
      (hπN _).mp (by change π (m - l m • x) = 0; rw [map_sub, hax, hl', sub_self])
    refine ⟨φ ∘ₗ ρ + ψ ∘ₗ l, LinearMap.ext fun m => ?_⟩
    simpa [LinearMap.add_apply, ← map_add, show ρ m + j ⟨l m, (hlp m).mpr m.2⟩ = m from
      Subtype.ext (sub_add_cancel _ _)] using
      congrArg (φ (ρ m) + ·) (LinearMap.congr_fun hψ ⟨l m, (hlp m).mpr m.2⟩)
  have hsurj : Function.Surjective Θ := fun q => by
    obtain ⟨ψ, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    let lN : N →ₗ[O] p := (l ∘ₗ N.subtype).codRestrict p fun m => (hlp m).mpr m.2
    have ht : l x - 1 ∈ p := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, hl', hx, sub_self]
    refine ⟨ψ ∘ₗ lN, (Submodule.Quotient.eq R).mpr
      ⟨LinearMap.toSpanSingleton O X (ψ ⟨l x - 1, ht⟩), LinearMap.ext fun a => ?_⟩⟩
    have h3 : lN (j a) = a + (a : O) • (⟨l x - 1, ht⟩ : p) := Subtype.ext (by
      change l ((a : O) • x) = (a : O) + (a : O) * (l x - 1); rw [map_smul, smul_eq_mul]; ring)
    simp only [LinearMap.lcomp_apply, Submodule.subtype_apply, LinearMap.toSpanSingleton_apply,
      LinearMap.sub_apply, LinearMap.comp_apply, h3, map_add, map_smul]; abel
  rw [← hker, Nat.card_congr (Θ.quotKerEquivOfSurjective hsurj).toEquiv,
    s5b7_ideal p hp0 X, Nat.card_congr e.toEquiv]

theorem s5b7_main (hO : ¬ IsField O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X]
    [Module.Projective O X] : ∀ (n : ℕ) (P M : Type) [AddCommGroup P] [Module O P] [AddCommGroup M]
    [Module O M] [Module.Finite O M] [Module.Projective O M] (ι : P →ₗ[O] M),
    Function.Injective ι → n ≠ 0 → Nat.card (M ⧸ LinearMap.range ι) = n →
    Nat.card ((P →ₗ[O] X) ⧸ LinearMap.range (LinearMap.lcomp O X ι)) = n ^ finrank O X := by
  intro n; induction n using Nat.strong_induction_on with | _ n ih => ?_
  intro P M _ _ _ _ _ _ ι hι hn0 hn; classical
  have : Infinite O := by
    by_contra h; exact hO (have := not_infinite_iff_finite.mp h; Finite.isField_of_domain O)
  rcases eq_top_or_exists_le_coatom (LinearMap.range ι) with htop | ⟨N, hN, hle⟩
  · let e := LinearEquiv.ofBijective ι ⟨hι, LinearMap.range_eq_top.mp htop⟩
    rw [LinearMap.range_eq_top.mpr fun φ => ⟨φ ∘ₗ e.symm.toLinearMap, LinearMap.ext fun y => by
      change φ (e.symm (e y)) = φ y; exact congrArg φ (e.symm_apply_apply y)⟩, ← hn, htop]; simp
  · let ι1 : P →ₗ[O] N := ι.codRestrict N fun y => hle ⟨y, rfl⟩
    have hc := s5b7_card_comp ι1 N.subtype N.injective_subtype
    rw [show N.subtype ∘ₗ ι1 = ι from rfl, hn, Submodule.range_subtype] at hc
    have hA : Nat.card (N ⧸ LinearMap.range ι1) ≠ 0 := left_ne_zero_of_mul (hc ▸ hn0)
    have : Finite (M ⧸ N) := Nat.finite_of_card_ne_zero (right_ne_zero_of_mul (hc ▸ hn0))
    have : Finite (N ⧸ LinearMap.range ι1) := Nat.finite_of_card_ne_zero hA
    have : Nontrivial (M ⧸ N) := Submodule.Quotient.nontrivial_iff.mpr hN.1
    have hlt : Nat.card (N ⧸ LinearMap.range ι1) < n :=
      hc ▸ lt_mul_of_one_lt_right (Nat.pos_of_ne_zero hA) Finite.one_lt_card
    have hinj : Function.Injective (LinearMap.lcomp O X ι1) :=
      fun φ₁ φ₂ hφ => LinearMap.ext fun y => by
        obtain ⟨a, b, hab, hEq⟩ := Finite.exists_ne_map_eq_of_infinite
          (fun a : O => (Submodule.Quotient.mk (a • y) : N ⧸ LinearMap.range ι1))
        obtain ⟨z, hz⟩ := (Submodule.Quotient.eq _).mp hEq; rw [← sub_smul] at hz
        exact smul_right_injective X (sub_ne_zero.mpr hab)
          (by simpa [hz, map_smul] using LinearMap.congr_fun hφ z)
    have : IsNoetherian O M := isNoetherian_of_isNoetherianRing_of_finite O M
    have : Module.Projective O N := s5b7_proj N
    have hc2 := s5b7_card_comp (LinearMap.lcomp O X N.subtype) (LinearMap.lcomp O X ι1) hinj
    rw [show LinearMap.lcomp O X ι1 ∘ₗ LinearMap.lcomp O X N.subtype =
          LinearMap.lcomp O X ι from rfl,
      ih _ hlt P N ι1 (fun _ _ h => hι (congrArg Subtype.val h)) hA rfl,
      s5b7_step hO M X N hN] at hc2
    rw [hc2, hc, mul_pow, mul_comm]

theorem cardCokernelRestriction :
    Formalism.HermitianLatticeCounting.LatticeSumBounds.HomRestrictIndex :=
  fun _ M X _ _ _ _ _ _ _ _ _ _ P hO _ => s5b7_main hO X _ P M P.subtype P.injective_subtype
    Nat.card_pos.ne' (by rw [Submodule.range_subtype])

end homRestrict

section volume
open Module Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate

lemma s5b7_gram_cons {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (r : ℕ) (v0 : V)
    (c : Fin r → ℂ) (w : Fin r → V) (hw : ∀ b, inner ℂ v0 (w b) = 0) :
    (Matrix.gram ℂ (Fin.cons v0 (fun b => c b • v0 + w b) : Fin (r + 1) → V)).det =
      ((‖v0‖ : ℂ) ^ 2) * (Matrix.gram ℂ w).det := by
  let v : Fin (r + 1) → V := Fin.cons v0 fun b => c b • v0 + w b
  let v' : Fin (r + 1) → V := Fin.cons v0 w; let cc : Fin (r + 1) → ℂ := Fin.cons 0 c
  have hvv' (i) : v i = cc i • v' 0 + v' i :=
    Fin.cases (by simp [v, v', cc]) (fun b => by simp [v, v', cc]) i
  change (Matrix.gram ℂ v).det = _
  rw [Matrix.det_eq_of_forall_row_eq_smul_add_const (B := Matrix.of fun i j => inner ℂ (v' i) (v j))
      (fun i => conj (cc i)) 0 (by simp [cc]) (fun i j => by
        simp only [Matrix.gram_apply, Matrix.of_apply, hvv' i, inner_add_left, inner_smul_left]
        ring), ← Matrix.det_transpose,
    Matrix.det_eq_of_forall_row_eq_smul_add_const (B := (Matrix.gram ℂ v')ᵀ) cc 0 (by simp [cc])
      (fun i j => by
        simp only [Matrix.transpose_apply, Matrix.of_apply, Matrix.gram_apply, hvv' i,
          inner_add_right, inner_smul_right]; ring),
    Matrix.det_transpose, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Finset.sum_eq_zero fun j _ => by simp [Matrix.gram_apply, v', hw j],
    show (Matrix.gram ℂ v').submatrix Fin.succ (Fin.succAbove 0) = Matrix.gram ℂ w by
      ext; simp [Matrix.gram_apply, v'], Matrix.gram_apply]
  simp [v', inner_self_eq_norm_sq_to_K]

lemma s5b7_exists_iso (d : ℕ) (u : EuclideanSpace ℂ (Fin (d + 1))) (hu : ‖u‖ = 1) :
    ∃ Φ : EuclideanSpace ℂ (Fin (d + 1)) ≃ₗᵢ[ℂ] WithLp 2 (ℂ × EuclideanSpace ℂ (Fin d)),
      Φ u = WithLp.toLp 2 (1, 0) := by
  have key (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
      (hW : finrank ℂ W = d + 1) (x : W) (hx : ‖x‖ = 1) :
      ∃ b : OrthonormalBasis (Fin (d + 1)) ℂ W, b 0 = x := by
    have ho : Orthonormal ℂ (({0} : Set (Fin (d + 1))).domRestrict fun _ => x) :=
      orthonormal_iff_ite.mpr fun i j =>
        Subsingleton.elim i j ▸ by simp [inner_self_eq_norm_sq_to_K, hx]
    exact (ho.exists_orthonormalBasis_extension_of_card_eq (by simpa using hW)).imp
      fun _ hb => hb 0 rfl
  obtain ⟨b, hb⟩ := key _ (by simp) u hu
  obtain ⟨b', hb'⟩ := key (WithLp 2 (ℂ × EuclideanSpace ℂ (Fin d)))
    (by rw [(WithLp.linearEquiv 2 ℂ _).finrank_eq]; simp [add_comm])
    (WithLp.toLp 2 (1, 0)) (by simp)
  exact ⟨b.repr.trans b'.repr.symm, by rw [← hb, ← hb']; simp⟩

lemma s5b7_finrank_real (n : ℕ) : finrank ℝ (EuclideanSpace ℂ (Fin n)) = 2 * n := by
  rw [(WithLp.linearEquiv 2 ℝ (Fin n → ℂ)).finrank_eq, Module.finrank_pi_fintype]; simp [mul_comm]

lemma s5b7_unit_ball (d : ℕ) :
    (volume : Measure (EuclideanSpace ℂ (Fin (d + 1)))).real (Metric.ball 0 1) =
      Real.pi ^ (d + 1) / ((d + 1).factorial : ℝ) := by
  simp only [Measure.real, InnerProductSpace.volume_ball, s5b7_finrank_real, ENNReal.ofReal_one,
    one_pow, one_mul]
  rw [pow_mul, Real.sq_sqrt Real.pi_pos.le, show ((2 * (d + 1) : ℕ) : ℝ) / 2 + 1 =
    ((d + 1 : ℕ) : ℝ) + 1 by push_cast; ring, Real.Gamma_nat_eq_factorial]
  exact ENNReal.toReal_ofReal (by positivity)

lemma s5b7_radial (d r : ℕ) (hr : r ≤ d) (R : ℝ) (hR : 0 < R) :
    ∫⁻ x : EuclideanSpace ℂ (Fin (d + 1)),
      ENNReal.ofReal (if ‖x‖ ≤ R then (‖x‖ ^ (2 * (d - r)))⁻¹ else 0) =
    ENNReal.ofReal (Real.pi ^ (d + 1) / (d.factorial : ℝ) * R ^ (2 * r + 2) / ((r : ℝ) + 1)) := by
  let φ (ρ : ℝ) : ℝ := if ρ ≤ R then (ρ ^ (2 * (d - r)))⁻¹ else 0
  let ψ : ℝ → ℝ := (Ioc 0 R).indicator fun ρ => ρ ^ (2 * r + 1)
  have hD := s5b7_finrank_real (d + 1)
  have heq : EqOn (fun ρ : ℝ => ρ ^ (finrank ℝ (EuclideanSpace ℂ (Fin (d + 1))) - 1) • φ ρ)
      ψ (Ioi 0) := fun ρ (hρ : 0 < ρ) => by
    by_cases h : ρ ≤ R
    · simp only [φ, ψ, hD, smul_eq_mul, h, ↓reduceIte, indicator_of_mem (mem_Ioc.mpr ⟨hρ, h⟩),
        show 2 * (d + 1) - 1 = 2 * (d - r) + (2 * r + 1) by omega, pow_add]; field_simp
    · simp [φ, ψ, h]
  have hint : Integrable fun x : EuclideanSpace ℂ (Fin (d + 1)) => φ ‖x‖ :=
    (integrable_fun_norm_addHaar volume).mpr
      (((continuous_pow _).integrableOn_Ioc.integrable_indicator
        measurableSet_Ioc).integrableOn.congr_fun heq.symm measurableSet_Ioi)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
      (.of_forall fun x => by simp only [φ]; split_ifs <;> positivity),
    integral_fun_norm_addHaar volume φ, setIntegral_congr_fun measurableSet_Ioi heq,
    s5b7_unit_ball, hD, setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.mpr Ioc_subset_Ioi_self, ← intervalIntegral.integral_of_le hR.le,
    integral_pow, Nat.factorial_succ]
  congr 1; simp only [zero_pow (by positivity : 2 * r + 1 + 1 ≠ 0), sub_zero, nsmul_eq_mul,
    smul_eq_mul]; push_cast; field_simp; ring

def s5b7_A (R : ℝ) (d r : ℕ) (t : ℝ) : Set (Fin r → EuclideanSpace ℂ (Fin d)) :=
  {a | (∀ b, ‖a b‖ ≤ R) ∧ Real.sqrt ‖(Matrix.gram ℂ a).det‖ ≤ t}

lemma s5b7_A_closed (R : ℝ) (d r : ℕ) (t : ℝ) : IsClosed (s5b7_A R d r t) := by
  have hc : Continuous fun a : Fin r → EuclideanSpace ℂ (Fin d) =>
      Real.sqrt ‖(Matrix.gram ℂ a).det‖ :=
    Real.continuous_sqrt.comp (continuous_norm.comp (Continuous.matrix_det
      (continuous_matrix fun i j => by
        simp only [Matrix.gram_apply]; exact (continuous_apply i).inner (continuous_apply j))))
  simpa only [s5b7_A, Set.ofPred_and, Set.ofPred_forall] using
    (isClosed_iInter fun b => isClosed_le (by fun_prop) continuous_const).inter
      (isClosed_le hc continuous_const)

lemma measurePreserving_pi_comp_prod {α β γ δ : Type*} [MeasureSpace α] [MeasureSpace β]
    [MeasureSpace γ] [MeasureSpace δ] [SigmaFinite (volume : Measure α)]
    [SigmaFinite (volume : Measure β)] [SigmaFinite (volume : Measure γ)]
    [SigmaFinite (volume : Measure δ)] (r : ℕ) (f : α → β) (g : β → γ × δ)
    (hf : MeasurePreserving f) (hg : MeasurePreserving g) :
    MeasurePreserving (fun a : Fin r → α =>
      ((fun b => (g (f (a b))).1), (fun b => (g (f (a b))).2))) volume volume :=
  (volume_measurePreserving_arrowProdEquivProdArrow γ δ (Fin r)).comp
    ((volume_preserving_pi fun _ : Fin r => hg).comp (volume_preserving_pi fun _ : Fin r => hf))

lemma s5b7_mp (d r : ℕ)
    (Φ : EuclideanSpace ℂ (Fin (d + 1)) ≃ₗᵢ[ℂ] WithLp 2 (ℂ × EuclideanSpace ℂ (Fin d))) :
    MeasurePreserving (fun a : Fin r → EuclideanSpace ℂ (Fin (d + 1)) =>
      ((fun b => (Φ (a b)).ofLp.1), (fun b => (Φ (a b)).ofLp.2))) volume volume :=
  measurePreserving_pi_comp_prod r _ _
    (LinearIsometryEquiv.measurePreserving
      ({ (Φ.toLinearEquiv.restrictScalars ℝ) with norm_map' := Φ.norm_map } :
        EuclideanSpace ℂ (Fin (d + 1)) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × EuclideanSpace ℂ (Fin d))))
    (WithLp.volume_preserving_ofLp ℂ (EuclideanSpace ℂ (Fin d)))

lemma s5b7_slice (R : ℝ) (d r : ℕ) (t : ℝ) (x : EuclideanSpace ℂ (Fin (d + 1))) (hx : x ≠ 0)
    (Φ : EuclideanSpace ℂ (Fin (d + 1)) ≃ₗᵢ[ℂ] WithLp 2 (ℂ × EuclideanSpace ℂ (Fin d)))
    (hΦ : Φ (((‖x‖⁻¹ : ℝ) : ℂ) • x) = WithLp.toLp 2 (1, 0))
    (a' : Fin r → EuclideanSpace ℂ (Fin (d + 1))) (h : (Fin.cons x a' :
      Fin (r + 1) → EuclideanSpace ℂ (Fin (d + 1))) ∈ s5b7_A R (d + 1) (r + 1) t) :
    (∀ b, ‖(Φ (a' b)).ofLp.1‖ ≤ R) ∧ (fun b => (Φ (a' b)).ofLp.2) ∈ s5b7_A R d r (t / ‖x‖) := by
  obtain ⟨hn, hg⟩ := h; have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hxc : ((‖x‖ : ℝ) : ℂ) ≠ 0 := mod_cast hx0.ne'
  have hΦx : Φ x = ((‖x‖ : ℝ) : ℂ) • WithLp.toLp 2 ((1 : ℂ), (0 : EuclideanSpace ℂ (Fin d))) := by
    rw [← hΦ, map_smul, smul_smul]; push_cast; rw [mul_inv_cancel₀ hxc, one_smul]
  refine ⟨fun b => (WithLp.norm_fst_le _ (Φ (a' b))).trans ((Φ.norm_map _).le.trans (hn b.succ)),
    fun b => (WithLp.norm_snd_le _ (Φ (a' b))).trans ((Φ.norm_map _).le.trans (hn b.succ)), ?_⟩
  let w (b : Fin r) : WithLp 2 (ℂ × EuclideanSpace ℂ (Fin d)) :=
    WithLp.toLp 2 (0, (Φ (a' b)).ofLp.2)
  let c (b : Fin r) : ℂ := (Φ (a' b)).ofLp.1 / (‖x‖ : ℂ)
  have hcons (k : Fin (r + 1)) : Φ ((Fin.cons x a' : Fin (r + 1) → _) k) =
      (Fin.cons (Φ x) (fun b => c b • Φ x + w b) : Fin (r + 1) → _) k :=
    Fin.cases rfl (fun b => by
      simp only [Fin.cons_succ, c, hΦx, smul_smul, div_mul_cancel₀ _ hxc]
      exact WithLp.ofLp_injective 2 (Prod.ext (by simp [w]) (by simp [w]))) k
  rw [show Matrix.gram ℂ (Fin.cons x a' : Fin (r + 1) → _) =
        Matrix.gram ℂ (Fin.cons (Φ x) fun b => c b • Φ x + w b) by
      ext i j; simp only [Matrix.gram_apply, ← Φ.inner_map_map, hcons],
    s5b7_gram_cons _ _ _ _ fun b => by simp [hΦx, w, WithLp.prod_inner_apply], Φ.norm_map,
    show Matrix.gram ℂ w = Matrix.gram ℂ fun b => (Φ (a' b)).ofLp.2 by
      ext; simp [Matrix.gram_apply, w, WithLp.prod_inner_apply],
    norm_mul, norm_pow, Complex.norm_real, norm_norm, Real.sqrt_mul (by positivity),
    Real.sqrt_sq hx0.le, mul_comm] at hg
  exact (le_div_iff₀ hx0).mpr hg

lemma s5b7_real_ineq (R t : ℝ) (hR : 0 < R) (ht : 0 ≤ t) (r d s : ℕ) (hs : s ≤ d) :
    (R ^ 2 * Real.pi) ^ r * (t ^ (2 * s) * R ^ (2 * r ^ 2) * Real.pi ^ (r * d) /
        (s.factorial : ℝ) ^ r) *
      (Real.pi ^ (d + 1) / (d.factorial : ℝ) * R ^ (2 * r + 2) / ((r : ℝ) + 1)) ≤
    t ^ (2 * s) * R ^ (2 * (r + 1) ^ 2) * Real.pi ^ ((r + 1) * (d + 1)) /
      (s.factorial : ℝ) ^ (r + 1) := by
  let _ := hR; have hs0 : (0 : ℝ) < s.factorial := mod_cast s.factorial_pos
  have h1 : (s.factorial : ℝ) ≤ (d.factorial : ℝ) * ((r : ℝ) + 1) :=
    (Nat.cast_le.mpr (Nat.factorial_le hs)).trans
      (le_mul_of_one_le_right (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) r]))
  calc _ = t ^ (2 * s) * R ^ (2 * (r + 1) ^ 2) * Real.pi ^ ((r + 1) * (d + 1)) /
          ((s.factorial : ℝ) ^ r * ((d.factorial : ℝ) * ((r : ℝ) + 1))) := by field_simp; ring
    _ ≤ _ := by rw [pow_succ (s.factorial : ℝ) r]; gcongr

theorem s5b7_vol (R : ℝ) (hR : 0 < R) : ∀ (r d : ℕ), r ≤ d → ∀ t : ℝ, 0 ≤ t →
    volume (s5b7_A R d r t) ≤ ENNReal.ofReal (t ^ (2 * (d - r)) * R ^ (2 * r ^ 2) *
      Real.pi ^ (r * d) / ((d - r).factorial : ℝ) ^ r) := by
  intro r; induction r with
  | zero =>
    intro d _ t ht; let _ := ht; by_cases h1 : 1 ≤ t
    · refine (measure_mono (subset_univ _)).trans ?_
      rw [Measure.volume_pi_eq_dirac 0, Measure.dirac_apply_of_mem (mem_univ _),
        ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by simpa using one_le_pow₀ h1)
    · rw [show s5b7_A R d 0 t = ∅ by ext; simpa [s5b7_A] using h1]; simp
  | succ r ih =>
    intro d hd t ht; obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    rw [Nat.succ_sub_succ_eq_sub]; set s := d - r with hs
    let E := EuclideanSpace ℂ (Fin (d + 1))
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => E) 0
    have hAm : MeasurableSet (s5b7_A R (d + 1) (r + 1) t) := (s5b7_A_closed _ _ _ _).measurableSet
    have hes (x) (a') : e.symm (x, a') = Fin.cons x a' := Fin.insertNth_zero' x a'
    rw [← ((volume_preserving_piFinSuccAbove _ 0).symm e).measure_preimage hAm.nullMeasurableSet,
      Measure.volume_eq_prod, Measure.prod_apply (e.symm.measurable hAm)]
    set C1 : ℝ := (R ^ 2 * Real.pi) ^ r * (t ^ (2 * s) * R ^ (2 * r ^ 2) * Real.pi ^ (r * d) /
        (s.factorial : ℝ) ^ r) with hC1def
    have hbound : ∀ᵐ x : E, volume (Prod.mk x ⁻¹' (e.symm ⁻¹' s5b7_A R (d + 1) (r + 1) t)) ≤
        ENNReal.ofReal C1 * ENNReal.ofReal (if ‖x‖ ≤ R then (‖x‖ ^ (2 * s))⁻¹ else 0) := by
      filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : E))] with x (hx : x ≠ 0)
      by_cases hxR : ‖x‖ ≤ R
      · simp only [hxR, ↓reduceIte]; have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
        obtain ⟨Φ, hΦ⟩ := s5b7_exists_iso d (((‖x‖⁻¹ : ℝ) : ℂ) • x)
          (by rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hx0.ne'])
        set S := (Set.pi univ fun _ : Fin r => Metric.closedBall (0 : ℂ) R) ×ˢ
          s5b7_A R d r (t / ‖x‖)
        have hSm : MeasurableSet S := (MeasurableSet.univ_pi fun _ =>
          Metric.isClosed_closedBall.measurableSet).prod (s5b7_A_closed _ _ _ _).measurableSet
        let proj (a : Fin r → E) := ((fun b => (Φ (a b)).ofLp.1), (fun b => (Φ (a b)).ofLp.2))
        calc volume (Prod.mk x ⁻¹' (e.symm ⁻¹' s5b7_A R (d + 1) (r + 1) t))
            ≤ volume (proj ⁻¹' S) := measure_mono fun a' ha' => by
                obtain ⟨h1, h2⟩ := s5b7_slice R d r t x hx Φ hΦ a' (hes x a' ▸ ha')
                exact ⟨fun b _ => by simpa [proj] using h1 b, h2⟩
          _ = ENNReal.ofReal ((R ^ 2 * Real.pi) ^ r) * volume (s5b7_A R d r (t / ‖x‖)) := by
              rw [(s5b7_mp d r Φ).measure_preimage hSm.nullMeasurableSet, Measure.volume_eq_prod,
                Measure.prod_prod, volume_pi_pi]
              simp only [Complex.volume_closedBall, Finset.prod_const, Finset.card_univ,
                Fintype.card_fin]
              rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by positivity),
                ENNReal.ofReal_pow hR.le, ← ENNReal.ofReal_coe_nnreal (p := NNReal.pi)]; rfl
          _ ≤ ENNReal.ofReal ((R ^ 2 * Real.pi) ^ r) * ENNReal.ofReal ((t / ‖x‖) ^ (2 * s) *
                R ^ (2 * r ^ 2) * Real.pi ^ (r * d) / (s.factorial : ℝ) ^ r) := by
              gcongr; exact ih d (by omega) _ (by positivity)
          _ = ENNReal.ofReal C1 * ENNReal.ofReal ((‖x‖ ^ (2 * s))⁻¹) := by
              rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
                hC1def, div_pow]; congr 1; field_simp
      · rw [show Prod.mk x ⁻¹' (e.symm ⁻¹' s5b7_A R (d + 1) (r + 1) t) = ∅ by
          ext a'; simp only [mem_preimage, mem_empty_iff_false, iff_false, hes]
          exact fun h => hxR (h.1 0)]; simp
    calc ∫⁻ x, volume (Prod.mk x ⁻¹' (e.symm ⁻¹' s5b7_A R (d + 1) (r + 1) t))
        ≤ _ := lintegral_mono_ae hbound
      _ = ENNReal.ofReal (C1 * (Real.pi ^ (d + 1) / d.factorial * R ^ (2 * r + 2) / (r + 1))) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hs, s5b7_radial d r (by omega) R hR,
            ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (s5b7_real_ineq R t hR ht r d s (Nat.sub_le d r))

end volume

end Formalism.HermitianLatticeCounting.P
