module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveVertPointLengthSteps
public import GroundTheory.HeightsAndTheta.Heights.Intersections.MultAtPosOfMemDivSupp
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CurveCountObjects

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

theorem CurveVertPointLength.of_single
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {s : MRing ι} {d : K → ℕ}
    (hs : IsMultiHomog s d)
    (hCh : ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ c : ∀ k, ι k, (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) →
      (curvePtIdeal y W).IsMaximal ∧
        (∀ p : Σ k, ι k, ∃ a b : curveRing y, b ∉ curvePtIdeal y W ∧
          (b : Ω) * (y p / y ⟨p.1, c p.1⟩) = a) ∧
        ∀ (e : K → ℕ) (g : MRing ι), IsMultiHomog g e →
          (g ∈ W ↔ ∃ a b : curveRing y, a ∈ curvePtIdeal y W ∧ b ∉ curvePtIdeal y W ∧
            (b : Ω) * aeval y g = (a : Ω) * ∏ k, y ⟨k, c k⟩ ^ e k))
    (hInj : Set.InjOn (curvePtIdeal y) (divSupp (mCoordIdeal y) s))
    (hSurj : ∀ m : Ideal (curveRing y), m.IsMaximal →
      locLen m (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) ≠ 0 →
      ∃ W ∈ divSupp (mCoordIdeal y) s, curvePtIdeal y W = m)
    (hMC : ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ c : ∀ k, ι k, (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) →
      ∀ a b : curveRing y, b ∉ curvePtIdeal y W →
        (b : Ω) * aeval y s = (a : Ω) * ∏ k, y ⟨k, c k⟩ ^ d k →
        multAt (mCoordIdeal y ⊔ Ideal.span {s}) W =
          locLen (curvePtIdeal y W) (curveRing y ⧸ Ideal.span {a}))
    (hSQ : ∀ (m : Ideal (curveRing y)) (c : ∀ k, ι k), m.IsPrime → (∀ k, y ⟨k, c k⟩ ≠ 0) →
      (∀ p : Σ k, ι k, ∃ a' b' : curveRing y, b' ∉ m ∧ (b' : Ω) * (y p / y ⟨p.1, c p.1⟩) = a') →
      ∀ a b : curveRing y, b ∉ m → (b : Ω) * aeval y s = (a : Ω) * ∏ k, y ⟨k, c k⟩ ^ d k →
        locLen m (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) =
          locLen m (curveRing y ⧸ Ideal.span {a})) :
    Set.BijOn (curvePtIdeal y) (divSupp (mCoordIdeal y) s)
        {m : Ideal (curveRing y) |
          m.IsMaximal ∧ locLen m (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) ≠ 0} ∧
      ∀ W ∈ divSupp (mCoordIdeal y) s,
        multAt (mCoordIdeal y ⊔ Ideal.span {s}) W =
          locLen (curvePtIdeal y W) (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) := by
  have hmax_mult : ∀ W ∈ divSupp (mCoordIdeal y) s,
      (curvePtIdeal y W).IsMaximal ∧
        multAt (mCoordIdeal y ⊔ Ideal.span {s}) W =
          locLen (curvePtIdeal y W) (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) := by
    intro W hW
    choose c hc using hW.2
    obtain ⟨hmax, hrat, hmem⟩ := hCh W hW c hc
    have hPW : mCoordIdeal y ≤ W := le_trans le_sup_left hW.1.1.2
    have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
    have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => ne_zero_of_X_notMem fun h => hc k (hPW h)
    obtain ⟨a, b, -, hb, hab⟩ := (hmem d s hs).mp hsW
    refine ⟨hmax, ?_⟩
    rw [hMC W hW c hc a b hb hab, ← hSQ _ c hmax.isPrime hyc hrat a b hb hab]
  refine ⟨⟨fun W hW => ?_, hInj, fun m hm => hSurj m hm.1 hm.2⟩,
    fun W hW => (hmax_mult W hW).2⟩
  obtain ⟨hmax, hmult⟩ := hmax_mult W hW
  exact ⟨hmax, hmult ▸ (IndefiniteRowSideFullHecke.Inter.multAt_pos_of_mem_divSupp hW).ne'⟩

theorem CurveVertPointLength.proof (hCh : CurveVertPointChart.Statement) (hInj : CurveVertPointInj.Statement)
    (hSurj : CurveVertPointSurj.Statement) (hMC : CurveVertPointMultChart.Statement)
    (hSQ : CurveSectionQuotLocal.Statement) : CurveVertPointLength.Statement :=
  fun K _ ι _ Ω _ y s d hP hs hsP =>
    CurveVertPointLength.of_single hs
      (fun W hW c hc => hCh K ι Ω y s d hP hs hsP W hW c hc)
      (hInj K ι Ω y s d hP hs hsP)
      (fun m hm hne => hSurj K ι Ω y s d hP hs hsP m hm hne)
      (fun W hW c hc a b hb hab => hMC K ι Ω y s d hP hs hsP W hW c hc a b hb hab)
      (fun m c hm hyc hrat a b hb hab => hSQ K ι Ω y s d hP hs hsP m c hm hyc hrat a b hb hab)

end

end GroundTheory.Heights₂.Heights.Targets
