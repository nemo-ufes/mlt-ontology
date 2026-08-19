import Experiments.Existence

/-!
# Experiment: singleton and union together

`INSIGHTS.md` §14 shows singleton, union and the constants are pairwise
independent, but it separates them with three *different* models — `Chain` has
singletons and no unions, `Pair` unions and no singletons, `Model.W` the
constants and neither. That leaves the obvious question open: can any domain
have singletons and unions at once, or do they conflict?

They do not conflict. This file gives a single model of **all** of them:
extensionality, grounding, singletons, unions, and the constants of `a13`–`a15`.

The model is the hereditarily finite sets, under Ackermann coding: an entity is
a natural number, and `a` is an instance of `b` exactly when bit `a` of `b` is
set. Extensionality is then the fact that a natural number is determined by its
bits; grounding is that a set bit of `m` is smaller than `m`; the singleton of
`a` is `2^a`; and the union is bitwise or. The individual is `0`, and the
constants are `1`, `2` and `4`.

So the three existence principles of §14 are jointly satisfiable, and adding all
of them to MLT* is consistent.
-/

namespace MLTStar.Existence

/-! ## Finite comprehension, abstractly

First the general fact the model is an instance of: singleton supplies the
points and union the gluing, so in *any* domain with both, every finite
non-empty list of entities is the extension of a type. `exists_pairType` was the
two-element case. -/

theorem exists_finiteType [Domain E] [SingletonClosed E] [UnionClosed E] :
    ∀ l : List E, l ≠ [] → ∃ t, ∀ x, iof x t ↔ x ∈ l
  | [], h => absurd rfl h
  | [a], _ => ⟨sing a, fun x => (iof_sing_iff a x).trans (by simp)⟩
  | a :: b :: rest, _ => by
      obtain ⟨t, ht⟩ := exists_finiteType (b :: rest) (by simp)
      obtain ⟨u, hu⟩ :=
        UnionClosed.exists_union (sing a) t (sing_isType a) ⟨b, (ht b).mpr (by simp)⟩
      exact ⟨u, fun x => (hu x).trans (by rw [iof_sing_iff, ht]; simp)⟩

namespace HF

/-! ## The hereditarily finite sets, Ackermann-coded -/

/-- An entity is a natural number, read as the set of its set bits. -/
structure HF where
  val : Nat
  deriving DecidableEq

instance : Domain HF := ⟨fun a b => b.val.testBit a.val = true⟩

theorem iof_iff {a b : HF} : iof a b ↔ b.val.testBit a.val = true := Iff.rfl

theorem eq_of_val {a b : HF} (h : a.val = b.val) : a = b := congrArg HF.mk h

/-! ### Bit lemmas -/

theorem eq_zero_of_no_bits {n : Nat} (h : ∀ i, n.testBit i = false) : n = 0 :=
  Nat.eq_of_testBit_eq fun i => by rw [h i]; simp

theorem exists_bit {n : Nat} (h : n ≠ 0) : ∃ i, n.testBit i = true := by
  apply Classical.byContradiction
  intro hno
  refine h (eq_zero_of_no_bits fun i => ?_)
  cases hb : n.testBit i with
  | false => rfl
  | true => exact absurd ⟨i, hb⟩ hno

/-- A number whose set bits are exactly `{k}` is `2 ^ k`. This handles both the
first- and second-order characterisations below. -/
theorem eq_two_pow_iff {n k : Nat} :
    (n ≠ 0 ∧ ∀ i, n.testBit i = true → i = k) ↔ n = 2 ^ k := by
  constructor
  · rintro ⟨hne, hall⟩
    refine Nat.eq_of_testBit_eq fun i => ?_
    rw [Nat.testBit_two_pow]
    cases hb : n.testBit i with
    | true => simp [hall i hb]
    | false =>
        obtain ⟨j, hj⟩ := exists_bit hne
        have hki : k ≠ i := by
          intro hEq
          have hbk : n.testBit k = true := by rw [← hall j hj]; exact hj
          rw [hEq, hb] at hbk
          exact Bool.noConfusion hbk
        simp [hki]
  · rintro rfl
    have hpos : 0 < 2 ^ k := Nat.pow_pos (by omega)
    refine ⟨by omega, fun i hi => ?_⟩
    rw [Nat.testBit_two_pow] at hi
    simp at hi
    omega

/-! ### Individuals and types -/

theorem individual_iff {x : HF} : Individual x ↔ x.val = 0 := by
  constructor
  · intro h
    refine eq_zero_of_no_bits fun i => ?_
    cases hb : x.val.testBit i with
    | false => rfl
    | true => exact absurd ⟨⟨i⟩, iof_iff.mpr hb⟩ h
  · intro hx ⟨y, hy⟩
    rw [iof_iff, hx] at hy
    simp at hy

theorem isType_iff {x : HF} : IsType x ↔ x.val ≠ 0 := by
  constructor
  · rintro ⟨y, hy⟩ hx
    rw [iof_iff, hx] at hy
    simp at hy
  · intro h
    obtain ⟨i, hi⟩ := exists_bit h
    exact ⟨⟨i⟩, iof_iff.mpr hi⟩

/-! ### The axioms -/

instance : Extensional HF where
  typeExtensionality t₁ t₂ _ _ h :=
    eq_of_val (Nat.eq_of_testBit_eq fun i => by
      by_cases hb : t₁.val.testBit i = true
      · have h2 : t₂.val.testBit i = true := iof_iff.mp ((h ⟨i⟩).mp (iof_iff.mpr hb))
        rw [hb, h2]
      · have h1 : t₁.val.testBit i = false := by simpa using hb
        have h2 : t₂.val.testBit i = false := by
          cases hc : t₂.val.testBit i with
          | false => rfl
          | true => exact absurd (iof_iff.mp ((h ⟨i⟩).mpr (iof_iff.mpr hc))) hb
        rw [h1, h2])

/-- A set bit of `m` is smaller than `m`, which is what makes `∈` well-founded
here and gives `a4`. -/
theorem lt_of_testBit {m a : Nat} (h : m.testBit a = true) : a < m :=
  Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.ge_two_pow_of_testBit h)

instance : Grounded HF where
  grounded S hne hty := by
    classical
    obtain ⟨y₀, hy₀⟩ := hne
    obtain ⟨m, hm, hmin⟩ :=
      MLTStar.Experiment.Chain.exists_least (fun k => S ⟨k⟩) y₀.val y₀.val hy₀ (Nat.le_refl _)
    obtain ⟨a, ha⟩ := exists_bit (isType_iff.mp (hty _ hm))
    exact ⟨⟨m⟩, hm, ⟨a⟩, iof_iff.mpr ha, hmin a (lt_of_testBit ha)⟩

/-! ### Singletons, unions, and the constants all hold -/

instance : SingletonClosed HF where
  exists_singleton x := ⟨⟨2 ^ x.val⟩, fun y => by
    rw [iof_iff, Nat.testBit_two_pow]
    constructor
    · intro h
      have hv : x.val = y.val := by simpa using h
      exact eq_of_val hv.symm
    · intro h; simp [h]⟩

instance : UnionClosed HF where
  exists_union t₁ t₂ _ _ := ⟨⟨t₁.val ||| t₂.val⟩, fun x => by
    rw [iof_iff, Nat.testBit_or]
    simp [iof_iff]⟩

theorem firstOrderType_iff {x : HF} : FirstOrderType x ↔ x.val = 1 := by
  rw [show (1 : Nat) = 2 ^ 0 from rfl, ← eq_two_pow_iff]
  constructor
  · exact fun h => ⟨isType_iff.mp h.1, fun i hi => individual_iff.mp (h.2 ⟨i⟩ (iof_iff.mpr hi))⟩
  · exact fun h => ⟨isType_iff.mpr h.1, fun y hy => individual_iff.mpr (h.2 y.val (iof_iff.mp hy))⟩

theorem secondOrderType_iff {x : HF} : SecondOrderType x ↔ x.val = 2 := by
  rw [show (2 : Nat) = 2 ^ 1 from rfl, ← eq_two_pow_iff]
  constructor
  · exact fun h => ⟨isType_iff.mp h.1, fun i hi => firstOrderType_iff.mp (h.2 ⟨i⟩ (iof_iff.mpr hi))⟩
  · exact fun h => ⟨isType_iff.mpr h.1, fun y hy => firstOrderType_iff.mpr (h.2 y.val (iof_iff.mp hy))⟩

instance : Constants HF where
  cIndividual := ⟨1⟩
  cFot := ⟨2⟩
  cSot := ⟨4⟩
  cIndividual_spec x := by
    rw [iof_iff, individual_iff, show (1 : Nat) = 2 ^ 0 from rfl, Nat.testBit_two_pow]
    simp [eq_comm]
  cFot_spec x := by
    rw [iof_iff, firstOrderType_iff, show (2 : Nat) = 2 ^ 1 from rfl, Nat.testBit_two_pow]
    simp [eq_comm]
  cSot_spec x := by
    rw [iof_iff, secondOrderType_iff, show (4 : Nat) = 2 ^ 2 from rfl, Nat.testBit_two_pow]
    simp [eq_comm]

/-- Singletons, unions and the constants are jointly satisfiable, on top of `a9`
and `a4`. -/
theorem consistent :
    ∃ (D : Type) (_ : Domain D) (_ : Extensional D) (_ : Grounded D)
      (_ : SingletonClosed D) (_ : UnionClosed D), Nonempty (Constants D) :=
  ⟨HF, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
   ⟨inferInstance⟩⟩

end HF

end MLTStar.Existence
