module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EiiUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.GeAlgTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocVanP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.XvanExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.TriComb
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PtPair
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem cob_of_coord {H k₀ k : Type} [Field k₀] [Field k] [Algebra k₀ k] (a : H → k₀) (z : H → k)
    (h : ∀ φ : k →ₗ[k₀] k₀, ∃ m, ∀ g, φ (z g) = a g * m - m) :
    ∃ m, ∀ g, z g = algebraMap k₀ k (a g) * m - m := by
  by_cases h1 : ∀ g, a g = 1
  · refine ⟨0, fun g => ?_⟩
    rw [mul_zero, sub_zero, ← Module.forall_dual_apply_eq_zero_iff k₀]
    intro φ
    obtain ⟨m, hm⟩ := h φ
    rw [hm, h1, one_mul, sub_self]
  · obtain ⟨g₀, hg₀⟩ := not_forall.mp h1
    have hne : a g₀ - 1 ≠ 0 := sub_ne_zero.mpr hg₀
    refine ⟨(a g₀ - 1)⁻¹ • z g₀, fun g => ?_⟩
    rw [← Algebra.smul_def, ← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff k₀]
    intro φ
    obtain ⟨m, hm⟩ := h φ
    simp only [map_sub, map_smul, hm, smul_eq_mul]
    field_simp
    ring

private theorem gen {Γ A V : Type} [TopologicalSpace Γ] [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing V]
    [IsLocalRing V] (f : A →+* V) [IsLocalHom f] (x : Γ → A) (hx : AdicCont (maximalIdeal A) x) (hne : ∃ g, x g ≠ 0) :
    ∃ (g1 : Γ) (c : Γ → V), x g1 ≠ 0 ∧ (∀ g, f (x g) = f (x g1) * c g) ∧ IsLocallyConstant fun g => residue V (c g) := by
  obtain ⟨g0, hg0⟩ := hne
  obtain ⟨g1, hg1⟩ : ∃ g1, ∀ g, x g1 ∣ x g := by
    obtain ⟨_, ⟨g1, rfl⟩, hmin⟩ := (wellFounded_lt (α := ℕ∞)).has_min
      (Set.range fun g => IsDiscreteValuationRing.addVal A (x g)) ⟨_, g0, rfl⟩
    exact ⟨g1, fun g => IsDiscreteValuationRing.addVal_le_iff_dvd.1 (not_lt.1 (hmin _ ⟨g, rfl⟩))⟩
  choose c hc using hg1
  have hb : x g1 ≠ 0 := fun h0 => hg0 (by rw [hc g0, h0, zero_mul])
  refine ⟨g1, fun g => f (c g), hb, fun g => by rw [← map_mul, ← hc], ?_⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 (hx (n + 1)) g] with y hy
  rw [Ideal.Quotient.eq, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hc y, hc g, ← mul_sub, hw,
    mul_assoc, Units.dvd_mul_left, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero n hϖ.ne_zero)] at hy
  rw [← sub_eq_zero, ← map_sub, ← map_sub, residue_eq_zero_iff]
  refine map_nonunit f _ ?_
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
  exact hy

private theorem locVan {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)
    (hD : D.Good) (hL : UpperTheory.V.Loc.LocalPublishedTheorems) (k : Type) [Field k] (red : c.O →+* k) (hred : ∀ a ∈ maximalIdeal c.O, red a = 0)
    (γ : G ℚ Ω →* c.Oˣ) (hγ : γ ∈ [D.al, D.be, D.th, D.al⁻¹, D.be⁻¹, D.th⁻¹]) (p : ℕ) (hp : p ∈ D.Sb) (z : D.Gp p → k)
    (hz : IsLocallyConstant z) (hco : ∀ g h : D.Gp p, z (g * h) = z g + red (γ g : c.O) * z h) :
    ∃ m, ∀ g : D.Gp p, z g = red (γ g : c.O) * m - m := by
  haveI : Finite (ResidueField c.O) := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1
  let f : ResidueField c.O →+* k := Ideal.Quotient.lift (maximalIdeal c.O) red hred
  letI : Algebra (ResidueField c.O) k := f.toAlgebra
  have hf : ∀ a : c.O, algebraMap (ResidueField c.O) k (residue c.O a) = red a := fun a => rfl
  have hs : ∀ (a : c.O) (x : k), red a * x = residue c.O a • x := fun a x => by
    rw [Algebra.smul_def, hf]
  have key := cob_of_coord (fun g : D.Gp p => Raw.bar γ g) z fun φ =>
    locVanP D hD hL _ (residue c.O) (fun a ha => (residue_eq_zero_iff a).2 ha) γ hγ p hp (fun g => φ (z g)) (hz.comp φ)
      (fun g h => by simp only [hco, hs, map_add (f := _), map_smul, smul_eq_mul])
  simpa only [hf] using key

private theorem core {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)
    (hD : D.Good) (hL : UpperTheory.V.Loc.LocalPublishedTheorems) (𝔞 : Amb l) (r : G ℚ Ω →* M4 𝔞.V) (u0 : M4 𝔞.V) (hr : KPair D 𝔞 r u0)
    (s u : Fin 4) (hE : Matrix.single s s (1 : 𝔞.V) ∈ Submodule.span 𝔞.V (Set.range r)) (hsu : lamW s ≠ lamW u)
    (hge : Ge r s u) (hmul : ∀ g h, r (g * h) s u = r g s s * r h s u + r g s u * r h u u) (v : 𝔞.V)
    (hl : ∀ g ∈ D.Gp l, r g s s * v + r g s u = (r g u s * v + r g u u) * v) : False := by
  have hne : s ≠ u := fun h => hsu (h ▸ rfl)
  obtain ⟨-, hsg, -, -, -, -, -, -, -, -, hcont, -⟩ := facts D hD
  obtain ⟨hsg1, -, hsg2⟩ := hsg l (Finset.mem_insert_self _ _)
  obtain ⟨a, hE⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hE
  obtain ⟨A, _, _, _, f, P, hf, hP, hPr⟩ := hr.small
  have hfr : ∀ g i j, f (P.r g i j) = r g i j := fun g i j => congrArg (fun Q : PD Unit _ _ => Q.r g i j) hPr
  haveI := hf.loc
  obtain ⟨g1, cc, hb, hc, hcl⟩ := gen f (fun g => P.r g s u) (hP s u) (by
    obtain ⟨g, hg⟩ := hge
    exact ⟨g, fun h => hg (by rw [← hfr, h, map_zero])⟩)
  simp only [hfr] at hc
  replace hb : r g1 s u ≠ 0 := fun h => hb (hf.inj (by rw [hfr, h, map_zero]))
  have hns := TriHelpers.lattice_of_min r (map_one r) s u hne a.support a (fun h => by
    rw [← hE, Finsupp.sum, Finset.sum_mul]
    simp only [map_mul, smul_mul_assoc]) g1 cc hb hc
  generalize r g1 s u = b at hb hc
  let red : c.O →+* 𝔞.k := 𝔞.red c
  haveI := 𝔞.loc c
  have hred : ∀ x : c.O, red x = 0 ↔ residue c.O x = 0 := fun x => by
    show residue 𝔞.V (𝔞.a c x) = 0 ↔ _
    rw [residue_eq_zero_iff, residue_eq_zero_iff, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
      isUnit_map_iff]
  have hred0 : ∀ x ∈ maximalIdeal c.O, red x = 0 := fun x hx => (hred x).2 ((residue_eq_zero_iff x).2 hx)
  have hdiag : ∀ g i, residue 𝔞.V (r g i i) = red (D.ps i g : c.O) := fun g i => by
    have := hr.red g i i
    rw [← sub_eq_zero]
    change residue 𝔞.V _ - residue 𝔞.V _ = 0
    rw [← map_sub, residue_eq_zero_iff]
    simpa [Raw.r0, diagRep] using this
  have hoff : ∀ g, residue 𝔞.V (r g u s) = 0 := fun g => by
    have := hr.red g u s
    rw [residue_eq_zero_iff]
    simpa [Raw.r0, diagRep, Matrix.diagonal_apply_ne _ hne.symm] using this
  have hU : ∀ g, red (D.ps u g : c.O) ≠ 0 := fun g => ((D.ps u g).isUnit.map red).ne_zero
  have hγ : ∀ g, red ((D.ps s * (D.ps u)⁻¹) g : c.O) = red (D.ps s g : c.O) / red (D.ps u g : c.O) := fun g => by
    rw [eq_div_iff (hU g), ← map_mul, ← Units.val_mul]
    simp
  let z : G ℚ Ω → 𝔞.k := fun g => residue 𝔞.V (cc g) / red (D.ps u g : c.O)
  have hzl : IsLocallyConstant z := by
    have a2 : IsLocallyConstant fun g => red (D.ps u g : c.O) :=
      (hcont u 1).comp (Ideal.Quotient.lift (maximalIdeal c.O ^ 1) red fun x hx => hred0 x (by simpa using hx))
    exact hcl.comp₂ a2 fun x y => x / y
  have hcoc : ∀ g h, z (g * h) = z g + red ((D.ps s * (D.ps u)⁻¹) g : c.O) * z h := fun g h => by
    have e : cc (g * h) = r g s s * cc h + cc g * r h u u := by
      apply mul_left_cancel₀ hb
      rw [← hc, hmul, hc g, hc h]
      ring
    simp only [z]
    rw [hγ, e, map_add (f := _), map_mul, map_mul, hdiag, hdiag, map_mul, Units.val_mul, map_mul]
    have := hU g
    have := hU h
    field_simp
    ring
  obtain ⟨m, hm⟩ := xvanExt D hD _ red hred0 _ (TriHelpers.root_mem D s u hsu) z hzl hcoc (by
      intro A hA g hg h1
      have e := hc g
      rw [hr.unr A hA g hg h1, Matrix.one_apply_ne hne] at e
      have : cc g = 0 := (mul_eq_zero.1 e.symm).resolve_left hb
      simp only [z, this, map_zero, zero_div]) (by
      intro p hp
      rcases Finset.mem_insert.1 hp with rfl | hp
      · have hd : red (D.ps u (D.sg p) : c.O) - red (D.ps s (D.sg p) : c.O) ≠ 0 := by
          rw [← map_sub, Ne, hred, map_sub, sub_eq_zero]
          exact hsg2 u s hsu.symm
        refine ⟨-(residue 𝔞.V (cc (D.sg p)) / (red (D.ps u (D.sg p) : c.O) - red (D.ps s (D.sg p) : c.O))), fun g hg => ?_⟩
        have e : residue 𝔞.V (cc g * (r (D.sg p) u u - r (D.sg p) s s) - cc (D.sg p) * (r g u u - r g s s)) = 0 := by
          have e1 := hl g hg
          have e2 := hl _ hsg1
          rw [hc] at e1 e2
          have e3 : cc g * (r (D.sg p) u u - r (D.sg p) s s) - cc (D.sg p) * (r g u u - r g s s) =
              cc (D.sg p) * v * r g u s + -(cc g * v * r (D.sg p) u s) := by
            apply mul_left_cancel₀ hb
            linear_combination (r (D.sg p) u s * v + r (D.sg p) u u - r (D.sg p) s s) * e1 - (r g u s * v + r g u u - r g s s) * e2
          rw [e3]
          simp only [map_add (f := _), map_neg, map_mul, hoff, mul_zero, neg_zero, add_zero]
        simp only [map_sub, map_mul, hdiag] at e
        simp only [z]
        rw [hγ]
        have := hU g
        field_simp
        linear_combination e
      · obtain ⟨m, hm⟩ := locVan D hD hL _ red hred0 _ (TriHelpers.root_mem D s u hsu) p hp (fun g => z g)
          (hzl.comp_continuous continuous_subtype_val) (fun g h => hcoc g h)
        exact ⟨m, fun g hg => hm ⟨g, hg⟩⟩)
  refine hns m fun g => ?_
  have := hm g
  simp only [z] at this
  rw [hγ, div_eq_iff (hU g)] at this
  rw [this, hdiag, hdiag]
  have := hU g
  field_simp

theorem UpperTheory.V.Ws.triV :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (𝔞 : Amb l) r, VPt D 𝔞 r → Irr (mapRep 𝔞.toK r) ∨ DiagType r ∨
      (Ge r 0 2 ∧ Ge r 2 0 ∧ ((∀ i j, lamW i < lamW j → ¬ Ge r i j) ∨ ∀ i j, lamW j < lamW i → ¬ Ge r i j)) := by
  intro hC Ω _ _ _ l _ c D hD 𝔞 r hr
  obtain ⟨u, hu⟩ := ptPair hC D hD 𝔞 r hr
  have push : ∀ {R R' : Type} [CommRing R] [CommRing R'] (y : R →+* R') (ρ : G ℚ Ω →* M4 R) (i : Fin 4),
      Matrix.single i i (1 : R) ∈ Submodule.span R (Set.range ρ) →
      Matrix.single i i (1 : R') ∈ Submodule.span R' (Set.range (mapRep y ρ)) := by
    intro R R' _ _ y ρ i h
    obtain ⟨b, hb⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 h
    have e : Matrix.single i i (1 : R') = ∑ g ∈ b.support, y (b g) • mapRep y ρ g := by
      ext p q
      have h2 := congrArg y (congrFun (congrFun hb p) q)

      rw [Finsupp.sum, Matrix.sum_apply, map_sum] at h2
      rw [Matrix.sum_apply]
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul, mapRep_apply] at h2 ⊢
      rw [h2, Matrix.single_apply, Matrix.single_apply]
      split_ifs <;> simp
    rw [e]
    exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
  have hE : ∀ i, Matrix.single i i (1 : 𝔞.V) ∈ Submodule.span 𝔞.V (Set.range r) := by
    obtain ⟨-, R, _, _, _, ρ, y, hρ, -, -, rfl⟩ := hr
    exact fun i => push y _ i (eii D hD R ρ hρ.mult hρ.nrm i)
  have hinj : Function.Injective 𝔞.toK := Subtype.val_injective
  have hadj : ∀ X : M4 𝔞.V, 𝔞.toK.mapMatrix (adj X) = adj (𝔞.toK.mapMatrix X) := fun X => by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adj_apply, map_zsmul]
  have hgsp : ∀ (ν : 𝔞.V) (X : M4 𝔞.V), IsGSp ν X → IsGSp (𝔞.toK ν) (𝔞.toK.mapMatrix X) := fun ν X h => by
    unfold IsGSp at h ⊢
    rw [← hadj, ← map_mul, h]
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hge : ∀ i j, Ge (mapRep 𝔞.toK r) i j ↔ Ge r i j := fun i j => by
    simp only [Ge, mapRep_apply, Ne, map_eq_zero_iff _ hinj]
  obtain ⟨-, grefl, gtr, h3, h5, -⟩ := geAlg 𝔞.K (mapRep 𝔞.toK r) _ (fun g => hgsp _ _ (hu.mult g)) fun i => push _ r i (hE i)
  simp only [hge] at grefl gtr h3 h5
  rw [h5]
  refine TriHelpers.tri_comb (Ge r) grefl gtr h3 fun i j hij gij gji => ?_
  by_contra hno
  have hne : i ≠ j := fun h => hij (h ▸ rfl)
  have hk : ∀ k, k ≠ i → k ≠ j → Ge r i k → Ge r k i → False := fun k a b x y => hno ⟨k, a, b, x, y⟩
  have hmul : ∀ a b, Ge r i a → Ge r b i → ∀ g h, r (g * h) a b = r g a i * r h i b + r g a j * r h j b := by
    intro a b ha hb g h
    rw [map_mul, Matrix.mul_apply, ← Finset.sum_pair (f := fun k => r g a k * r h k b) hne]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk' => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk'
    by_contra h0
    rw [mul_eq_zero, not_or] at h0
    exact hk k hk'.1 hk'.2 (gtr _ _ _ ha ⟨g, h0.1⟩) (gtr _ _ _ ⟨h, h0.2⟩ hb)
  have hu1 : adj u * u = 1 := by simpa [IsGSp] using hu.sp
  let U : (M4 𝔞.K)ˣ := Units.map 𝔞.toK.mapMatrix.toMonoidHom ⟨adj u, u, hu1, mul_eq_one_comm.1 hu1⟩
  have z0 : ∀ x : 𝔞.V, x = 0 → 𝔞.toK x = 0 := fun x h => by rw [h, map_zero]
  obtain ⟨x, y, φ, hxy, hφ⟩ := TriHelpers.line (fun g : D.Gp l => 𝔞.toK.mapMatrix (r g)) U
    (fun g a b h => by
      show (𝔞.toK.mapMatrix (adj u) * 𝔞.toK.mapMatrix (r g) * 𝔞.toK.mapMatrix u) a b = 0
      rw [← map_mul, ← map_mul]
      exact z0 _ (hu.flag g g.2 a b h))
    (fun k => Ge r k i) i j hne (grefl i)
    (fun g a b hb ha => z0 _ (by_contra fun h => ha (gtr _ _ _ ⟨g, h⟩ hb)))
    (fun g k h a b => ⟨z0 _ (by_contra fun h' => hk k a b ⟨g, h'⟩ h),
      z0 _ (by_contra fun h' => hk k a b (gtr _ _ _ gij ⟨g, h'⟩) h)⟩)
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at hφ
  have hv : (y ≠ 0 ∧ x / y ∈ 𝔞.V) ∨ (x ≠ 0 ∧ y / x ∈ 𝔞.V) := by
    by_cases hy : y = 0
    · exact Or.inr ⟨hxy.resolve_right (not_not.2 hy), by rw [hy, zero_div]; exact zero_mem _⟩
    by_cases hx : x = 0
    · exact Or.inl ⟨hy, by rw [hx, zero_div]; exact zero_mem _⟩
    rcases 𝔞.V.mem_or_inv_mem (x / y) with h | h
    · exact Or.inl ⟨hy, h⟩
    · exact Or.inr ⟨hx, by rwa [inv_div] at h⟩
  rcases hv with ⟨hy, h⟩ | ⟨hx, h⟩
  · refine core D hD hC.loc 𝔞 r u hu i j (hE i) hij gij (hmul i j (grefl i) gji) ⟨x / y, h⟩ fun g hg => hinj ?_
    obtain ⟨e1, e2⟩ := hφ ⟨g, hg⟩
    have e : 𝔞.toK ⟨x / y, h⟩ = x / y := rfl
    simp only [map_add (f := _), map_mul, e] at e1 e2 ⊢
    field_simp
    linear_combination y * e1 - x * e2
  · refine core D hD hC.loc 𝔞 r u hu j i (hE j) hij.symm gji (fun g h => by rw [hmul j i gij (grefl i), add_comm])
      ⟨y / x, h⟩ fun g hg => hinj ?_
    obtain ⟨e1, e2⟩ := hφ ⟨g, hg⟩
    have e : 𝔞.toK ⟨y / x, h⟩ = y / x := rfl
    simp only [map_add (f := _), map_mul, e] at e1 e2 ⊢
    field_simp
    linear_combination x * e2 - y * e1
