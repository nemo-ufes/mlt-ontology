import MLTStar

/-!
# Experiment: what makes types exist

The most under-specified part of MLT* is *which types there are*. The theory is
rich about the structure of types — orders, powertypes, categorization,
partitioning — and nearly silent about their existence. `IsPowertypeOf` is a
*defined relation*, never asserted to be inhabited, so in the base theory the
only types whose existence is claimed at all are the three constants of
`a13`–`a15`. Everything else is conditional: *if* such types exist, then…

This file corrects a claim in `INSIGHTS.md` §10 and then explores the gap.

## The correction

§10 said the types have no meets or joins "since that would need exactly the
comprehension the theory cannot have". That conflates two different things.

* **Joins are fine.** A binary union is a bounded operation, nothing like
  unrestricted comprehension, and it does not reproduce Russell's argument. Add
  it and the types become a join-semilattice (§4).
* **Meets fail for an unrelated reason.** MLT* *defines* `Individual x` as "`x`
  has no instances", so an entity with empty extension is an individual, not an
  empty type. Two types with disjoint extensions therefore have no meet — not
  because of comprehension, but because the theory's individual/type dichotomy
  leaves no room for an empty type (§2, §3).

## The payoff

Union closure is not merely harmless. Together with the constants it *forces*
orderless types to exist (§5), where `MLTStar/Model.lean` shows the base axioms
merely permit them. So a single bounded existence principle turns basic MLT into
MLT*, which is a much more satisfying account of where orderless types come from
than positing them.
-/

namespace MLTStar.Existence

universe u
variable {E : Type u} [Domain E]

/-! ## 1. A type with mixed instances is orderless

The lemma the rest of the file runs on. A basic type is either the type of all
individuals or a Cardelli powertype; the first has only individuals as
instances, the second only types. So a type having *both* an individual and a
type among its instances can specialize neither, and no induction is needed. -/

theorem not_orderedType_of_mixed {u i t : E}
    (hi : iof i u) (hind : Individual i) (ht : iof t u) (htype : IsType t) :
    ¬ OrderedType u := by
  rintro ⟨b, hb, hs⟩
  cases hb with
  | individuals hbi => exact ((hbi t).mp (hs.2 t ht)) htype
  | powertype _ hp => exact hind ((hp.2 i).mp (hs.2 i hi)).isType_left

theorem orderlessType_of_mixed {u i t : E}
    (hi : iof i u) (hind : Individual i) (ht : iof t u) (htype : IsType t) :
    OrderlessType u :=
  ⟨⟨i, hi⟩, not_orderedType_of_mixed hi hind ht htype⟩

/-! ## 2. There is no empty type

Not an axiom and not an oversight: `Individual` is *defined* as having no
instances, so "empty type" is a contradiction in terms. This is what obstructs
meets, and it has nothing to do with comprehension. -/

theorem no_empty_type {x : E} (h : ∀ y, ¬ iof y x) : Individual x := fun ⟨y, hy⟩ => h y hy

theorem not_isType_of_empty {x : E} (h : ∀ y, ¬ iof y x) : ¬ IsType x := no_empty_type h

/-! ## 3. Meets are inherently partial

Two types with disjoint extensions have no greatest lower bound, because the
only candidate would have to be empty. -/

/-- `m` is the intersection of `t₁` and `t₂`. -/
def IsMeetOf (m t₁ t₂ : E) : Prop := ∀ x, iof x m ↔ (iof x t₁ ∧ iof x t₂)

theorem no_meet_of_disjoint {t₁ t₂ : E} (hd : ∀ x, ¬ (iof x t₁ ∧ iof x t₂)) :
    ¬ ∃ m, IsType m ∧ IsMeetOf m t₁ t₂ := by
  rintro ⟨m, hm, hmeet⟩
  obtain ⟨y, hy⟩ := hm
  exact hd y ((hmeet y).mp hy)

/-- Disjointness is not exotic: any type that disjointly categorizes something
has pairwise-disjoint instances, so meets are missing exactly where MLT*'s own
partitioning notion applies. -/
theorem no_meet_of_disjointlyCategorizes {c t a b : E}
    (h : DisjointlyCategorizes c t) (ha : iof a c) (hb : iof b c) (hne : a ≠ b) :
    ¬ ∃ m, IsType m ∧ IsMeetOf m a b :=
  no_meet_of_disjoint fun x hx => hne (h.2 x a b ha hb hx.1 hx.2)

/-! ## 4. Joins are fine

A binary union is bounded — it names no predicate the theory did not already
have extensions for — and it is the least upper bound in the specialization
order. Adding it makes the types a join-semilattice. -/

/-- Every pair of types has a union. -/
class UnionClosed (E : Type u) [Domain E] : Prop where
  exists_union : ∀ t₁ t₂ : E, IsType t₁ → IsType t₂ →
    ∃ u, ∀ x, iof x u ↔ (iof x t₁ ∨ iof x t₂)

/-- `u` is the union of `t₁` and `t₂`. -/
def IsJoinOf (u t₁ t₂ : E) : Prop := ∀ x, iof x u ↔ (iof x t₁ ∨ iof x t₂)

theorem IsJoinOf.isType {u t₁ t₂ : E} (h : IsJoinOf u t₁ t₂) (ht : IsType t₁) : IsType u :=
  let ⟨y, hy⟩ := ht; ⟨y, (h y).mpr (Or.inl hy)⟩

theorem IsJoinOf.le_left {u t₁ t₂ : E} (h : IsJoinOf u t₁ t₂) (ht : IsType t₁) :
    Specializes t₁ u := ⟨ht, fun x hx => (h x).mpr (Or.inl hx)⟩

theorem IsJoinOf.le_right {u t₁ t₂ : E} (h : IsJoinOf u t₁ t₂) (ht : IsType t₂) :
    Specializes t₂ u := ⟨ht, fun x hx => (h x).mpr (Or.inr hx)⟩

/-- …and it really is the *least* upper bound. -/
theorem IsJoinOf.least {u t₁ t₂ v : E} (h : IsJoinOf u t₁ t₂)
    (h₁ : Specializes t₁ v) (h₂ : Specializes t₂ v) (hu : IsType u) : Specializes u v :=
  ⟨hu, fun x hx => ((h x).mp hx).elim (h₁.2 x) (h₂.2 x)⟩

/-! ## 5. Union closure forces orderless types to exist

The type of all individuals has an individual among its instances; the type of
all first-order types has `cIndividual`, a *type*, among its instances. Their
union therefore has both, and §1 makes it orderless.

So where `MLTStar/Model.lean` shows the base axioms permit a purely ordered
model, adding binary unions rules that model out. One bounded existence
principle takes basic MLT to MLT*. -/

theorem exists_orderlessType [Constants E] [UnionClosed E] : ∃ u : E, OrderlessType u := by
  obtain ⟨i, hind⟩ := exists_individual (E := E)
  obtain ⟨u, hu⟩ :=
    UnionClosed.exists_union (cIndividual : E) (cFot : E) cIndividual_isType cFot_isType
  refine ⟨u, orderlessType_of_mixed (i := i) (t := cIndividual) ?_ hind ?_ cIndividual_isType⟩
  · exact (hu i).mpr (Or.inl ((iof_cIndividual_iff i).mpr hind))
  · exact (hu _).mpr (Or.inr iof_cIndividual_cFot)

/-! ## 6. Union closure is consistent

Cheaply: one individual and one type. There is only one type, so every union is
already present. This says nothing about combining unions with the constants —
§5 shows that combination is what has real content — but it does show unions are
not self-defeating the way comprehension is. -/

namespace Pair

inductive P where
  | i | t
  deriving DecidableEq, Repr

def piof (a b : P) : Prop := a = .i ∧ b = .t

instance : Domain P := ⟨piof⟩
instance (a b : P) : Decidable (piof a b) := by unfold piof; infer_instance
instance (a b : P) : Decidable (iof a b) := inferInstanceAs (Decidable (piof a b))

instance instForall (p : P → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p .i ∧ p .t) ⟨fun h x => by cases x <;> simp_all, fun h => ⟨h _, h _⟩⟩

instance instExists (p : P → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  decidable_of_iff (p .i ∨ p .t)
    ⟨fun h => by rcases h with h | h <;> exact ⟨_, h⟩, fun ⟨x, hx⟩ => by cases x <;> simp_all⟩

instance (x : P) : Decidable (IsType x) := inferInstanceAs (Decidable (∃ y, iof y x))

theorem not_isType_i : ¬ IsType P.i := by decide
theorem isType_iff : ∀ x : P, IsType x ↔ x = P.t := by decide

instance : Extensional P where
  typeExtensionality := by decide

instance : Grounded P where
  grounded S hne hty := by
    by_cases h : S .t
    · exact ⟨.t, h, .i, by decide, fun hs => not_isType_i (hty _ hs)⟩
    · obtain ⟨y, hy⟩ := hne
      cases y
      · exact absurd (hty _ hy) not_isType_i
      · exact absurd hy h

instance : UnionClosed P where
  exists_union t₁ t₂ h₁ h₂ := by
    rw [isType_iff] at h₁ h₂
    subst h₁; subst h₂
    exact ⟨.t, by decide⟩

theorem consistent :
    ∃ (D : Type) (_ : Domain D) (_ : Extensional D) (_ : Grounded D),
      Nonempty (UnionClosed D) :=
  ⟨P, inferInstance, inferInstance, inferInstance, ⟨inferInstance⟩⟩

end Pair

/-! ## 7. What union closure does *not* give

Binary union is finitary, so it does not produce the constants: `cIndividual`
collects *all* individuals, which is an infinitary union and not reachable by
iterating a binary one. The two existence principles are independent — unions
generate orderless types from types already present, the constants supply the
ordered ones, and neither substitutes for the other. -/

end MLTStar.Existence
