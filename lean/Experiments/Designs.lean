import MLTStar

/-!
# Experiment: alternative designs

Three questions about the shape of MLT*, each answered by a proof rather than an
argument. Like `NoConstants.lean`, nothing in `MLTStar/` imports this.

1. **Specialization wants to live on the types, not on the entities.** On the
   full domain it is not even reflexive; restricted to the types it is a partial
   order (§1). That is a presentational change with no logical cost, and it is
   what lets §2 be stated.

2. **The powertype is an order embedding, not merely monotone.** `t3` says
   specialization is preserved; it is in fact *reflected* too (§2). So the
   stratification is the orbit of one injective, monotone, fixed-point-free
   operator on a poset — which is a considerably smaller thing to describe than
   `a10` plus `t1`–`t3` plus the constants.

3. **The axioms are independent.** Neither `a9` nor `a4` follows from the rest
   (§3, §4), so nothing here is redundant. Together with `Collapse` in
   `NoConstants.lean` — a model of `a9` and `a4` with no type of individuals —
   all three are pairwise independent.
-/

namespace MLTStar.Design

universe u
variable {E : Type u} [Domain E]

/-! ## 1. Specialization is a partial order on the types

`Specializes` is reflexive only on types: an individual specializes nothing,
itself included. Restricting to the subtype of types is what turns it into an
order, and it is the natural carrier for everything in §2. -/

/-- The types of a domain. -/
abbrev Ty (E : Type u) [Domain E] := {x : E // IsType x}

instance : LE (Ty E) := ⟨fun a b => Specializes a.1 b.1⟩

theorem Ty.le_def {a b : Ty E} : a ≤ b ↔ Specializes a.1 b.1 := Iff.rfl

theorem Ty.le_refl (a : Ty E) : a ≤ a := Specializes.refl a.2

theorem Ty.le_trans {a b c : Ty E} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  Specializes.trans h₁ h₂

theorem Ty.le_antisymm [Extensional E] {a b : Ty E} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b :=
  Subtype.ext (Specializes.antisymm h₁ h₂)

/-- On the full domain it is *not* an order: individuals are not reflexive. -/
theorem not_specializes_self_of_individual {x : E} (h : Individual x) :
    ¬ Specializes x x := fun hs => h hs.1

/-! ## 2. The powertype is an order embedding

`t3` gives one direction. The other holds because a base type always
instantiates its own powertype, so `p₁ ⊑ p₂` applied at `t₁` yields `t₁ ⊑ t₂`
directly. Nothing but `a10` is needed. -/

/-- Specialization between powertypes is *equivalent* to specialization between
their base types. `t3` is the left-to-right half. -/
theorem specializes_powertype_iff {p₁ p₂ t₁ t₂ : E}
    (h₁ : IsPowertypeOf p₁ t₁) (h₂ : IsPowertypeOf p₂ t₂) :
    Specializes p₁ p₂ ↔ Specializes t₁ t₂ :=
  ⟨fun h => (h₂.2 t₁).mp (h.2 t₁ h₁.iof_base), fun h => t3 h h₁ h₂⟩

/-- Reflecting specialization gives injectivity up to `a9` — a second proof of
`t2_powertypeUnique`, now as a property of the operator rather than a fact about
each powertype. -/
theorem powertype_injective [Extensional E] {p t₁ t₂ : E}
    (h₁ : IsPowertypeOf p t₁) (h₂ : IsPowertypeOf p t₂) : t₁ = t₂ :=
  Specializes.antisymm
    ((specializes_powertype_iff h₁ h₂).mp (Specializes.refl h₁.1))
    ((specializes_powertype_iff h₂ h₁).mp (Specializes.refl h₂.1))

/-- Base types are strictly below their powertypes: `t ⊏ ℘t` is proper, since a
type is never its own powertype. -/
theorem properSpecializes_powertype [Grounded E] {p t : E}
    (h : IsPowertypeOf p t) (hs : Specializes t p) : ProperSpecializes t p :=
  ⟨hs, fun heq => h.ne heq.symm⟩

/-! ## 3. `a9` is independent

A five-element domain with two distinct but coextensive types of individuals.
It satisfies `a4` and the constants — `Constants` only asks that *some* type has
exactly the individuals as instances, and picks one — but not extensionality. -/

namespace NoExt

/-- `I` individual; `C` and `C'` both have exactly `I` as an instance; `F` has
both; `S` has `F`. -/
inductive X where
  | I | C | C' | F | S
  deriving DecidableEq, Repr

def xiof (a b : X) : Prop :=
  (a = .I ∧ (b = .C ∨ b = .C')) ∨ ((a = .C ∨ a = .C') ∧ b = .F) ∨ (a = .F ∧ b = .S)

instance : Domain X := ⟨xiof⟩
instance (a b : X) : Decidable (xiof a b) := by unfold xiof; infer_instance
instance (a b : X) : Decidable (iof a b) := inferInstanceAs (Decidable (xiof a b))

instance instForall (p : X → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p .I ∧ p .C ∧ p .C' ∧ p .F ∧ p .S)
    ⟨fun h x => by cases x <;> simp_all, fun h => ⟨h _, h _, h _, h _, h _⟩⟩

instance instExists (p : X → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  decidable_of_iff (p .I ∨ p .C ∨ p .C' ∨ p .F ∨ p .S)
    ⟨fun h => by rcases h with h | h | h | h | h <;> exact ⟨_, h⟩,
     fun ⟨x, hx⟩ => by cases x <;> simp_all⟩

instance (x : X) : Decidable (IsType x) := inferInstanceAs (Decidable (∃ y, iof y x))
instance (x : X) : Decidable (Individual x) := inferInstanceAs (Decidable (¬ ∃ y, iof y x))
instance (x : X) : Decidable (FirstOrderType x) :=
  inferInstanceAs (Decidable (IsType x ∧ ∀ y, iof y x → Individual y))
instance (x : X) : Decidable (SecondOrderType x) :=
  inferInstanceAs (Decidable (IsType x ∧ ∀ y, iof y x → FirstOrderType y))

theorem not_isType_I : ¬ IsType X.I := by decide

instance : Constants X where
  cIndividual := .C
  cFot := .F
  cSot := .S
  cIndividual_spec := by decide
  cFot_spec := by decide
  cSot_spec := by decide

instance : Grounded X where
  grounded S hne hty := by
    by_cases hC : S .C
    · exact ⟨.C, hC, .I, by decide, fun h => not_isType_I (hty _ h)⟩
    · by_cases hC' : S .C'
      · exact ⟨.C', hC', .I, by decide, fun h => not_isType_I (hty _ h)⟩
      · by_cases hF : S .F
        · exact ⟨.F, hF, .C, by decide, hC⟩
        · by_cases hS : S .S
          · exact ⟨.S, hS, .F, by decide, hF⟩
          · obtain ⟨y, hy⟩ := hne
            cases y
            · exact absurd (hty _ hy) not_isType_I
            · exact absurd hy hC
            · exact absurd hy hC'
            · exact absurd hy hF
            · exact absurd hy hS

/-- `C` and `C'` are distinct types with the same instances. -/
theorem not_extensional :
    ¬ ∀ t₁ t₂ : X, IsType t₁ → IsType t₂ → (∀ x, iof x t₁ ↔ iof x t₂) → t₁ = t₂ := by
  decide

end NoExt

/-- `a9` does not follow from `a4` and `a13`–`a15`. -/
theorem extensional_independent :
    ∃ (D : Type) (_ : Domain D) (_ : Grounded D) (_ : Constants D),
      ¬ ∀ t₁ t₂ : D, IsType t₁ → IsType t₂ → (∀ x, iof x t₁ ↔ iof x t₂) → t₁ = t₂ :=
  ⟨NoExt.X, inferInstance, inferInstance, inferInstance, NoExt.not_extensional⟩

/-! ## 4. `a4` is independent

The four-element model with one self-supporting type bolted on: `u` whose only
instance is `u`. Extensionality and the constants survive — `u` is neither
first- nor second-order, so it disturbs nothing — but the class `{u}` is a
non-empty class of types closed under instantiation, which is exactly what `a4`
forbids. -/

namespace NoGrounding

inductive Y where
  | ind | cInd | cFot | cSot | u
  deriving DecidableEq, Repr

def yiof (a b : Y) : Prop :=
  (a = .ind ∧ b = .cInd) ∨ (a = .cInd ∧ b = .cFot) ∨ (a = .cFot ∧ b = .cSot) ∨
  (a = .u ∧ b = .u)

instance : Domain Y := ⟨yiof⟩
instance (a b : Y) : Decidable (yiof a b) := by unfold yiof; infer_instance
instance (a b : Y) : Decidable (iof a b) := inferInstanceAs (Decidable (yiof a b))

instance instForall (p : Y → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p .ind ∧ p .cInd ∧ p .cFot ∧ p .cSot ∧ p .u)
    ⟨fun h x => by cases x <;> simp_all, fun h => ⟨h _, h _, h _, h _, h _⟩⟩

instance instExists (p : Y → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  decidable_of_iff (p .ind ∨ p .cInd ∨ p .cFot ∨ p .cSot ∨ p .u)
    ⟨fun h => by rcases h with h | h | h | h | h <;> exact ⟨_, h⟩,
     fun ⟨x, hx⟩ => by cases x <;> simp_all⟩

instance (x : Y) : Decidable (IsType x) := inferInstanceAs (Decidable (∃ y, iof y x))
instance (x : Y) : Decidable (Individual x) := inferInstanceAs (Decidable (¬ ∃ y, iof y x))
instance (x : Y) : Decidable (FirstOrderType x) :=
  inferInstanceAs (Decidable (IsType x ∧ ∀ y, iof y x → Individual y))
instance (x : Y) : Decidable (SecondOrderType x) :=
  inferInstanceAs (Decidable (IsType x ∧ ∀ y, iof y x → FirstOrderType y))

instance : Extensional Y where
  typeExtensionality := by decide

instance : Constants Y where
  cIndividual := .cInd
  cFot := .cFot
  cSot := .cSot
  cIndividual_spec := by decide
  cFot_spec := by decide
  cSot_spec := by decide

theorem u_isType : IsType Y.u := by decide
theorem iof_u_iff : ∀ z : Y, iof z Y.u ↔ z = Y.u := by decide

/-- `{u}` is a non-empty class of types with no instance outside it. -/
theorem not_grounded :
    ¬ ∀ S : Y → Prop, (∃ y, S y) → (∀ y, S y → IsType y) →
        ∃ y, S y ∧ ∃ z, iof z y ∧ ¬ S z := by
  intro h
  obtain ⟨y, hy, z, hz, hzn⟩ :=
    h (fun w => w = Y.u) ⟨Y.u, rfl⟩ (fun w hw => hw ▸ u_isType)
  exact hzn ((iof_u_iff z).mp (hy ▸ hz))

end NoGrounding

/-- `a4` does not follow from `a9` and `a13`–`a15`. -/
theorem grounded_independent :
    ∃ (D : Type) (_ : Domain D) (_ : Extensional D) (_ : Constants D),
      ¬ ∀ S : D → Prop, (∃ y, S y) → (∀ y, S y → IsType y) →
          ∃ y, S y ∧ ∃ z, iof z y ∧ ¬ S z :=
  ⟨NoGrounding.Y, inferInstance, inferInstance, inferInstance, NoGrounding.not_grounded⟩

/-! ## 5. Why the theory can afford only the powertype

MLT* is strikingly ungenerous about which types exist: the constants, and
powertypes. It is worth seeing that this is forced rather than timid.

An unrestricted comprehension principle — every class of entities is the
extension of some type — is inconsistent outright, by Russell's argument
applied to instantiation. And the obvious repair, separation, is inconsistent
*with orderless types*: a universal type plus separation reproduces the same
contradiction. Since a universal type is exactly what MLT* was extended to
admit, the theory cannot have either, and the powertype is what is left. -/

/-- Unrestricted comprehension is inconsistent: take the class of entities that
do not instantiate themselves. -/
theorem no_comprehension : ¬ ∀ P : E → Prop, ∃ t : E, ∀ x, iof x t ↔ P x := by
  intro h
  obtain ⟨t, ht⟩ := h (fun x => ¬ iof x x)
  exact (fun hn => hn ((ht t).mpr hn)) (fun hp => (ht t).mp hp hp)

/-- Separation — carving a type out of the instances of an existing type — is
inconsistent as soon as a universal type exists. So MLT*'s orderless types and
a separation principle cannot be had together. -/
theorem no_separation_with_universal {u : E} (hu : ∀ e : E, iof e u) :
    ¬ ∀ (t : E) (P : E → Prop), ∃ s : E, ∀ x, iof x s ↔ (iof x t ∧ P x) := by
  intro h
  obtain ⟨s, hs⟩ := h u (fun x => ¬ iof x x)
  have hiff : iof s s ↔ ¬ iof s s :=
    ⟨fun hp => ((hs s).mp hp).2, fun hn => (hs s).mpr ⟨hu s, hn⟩⟩
  exact (fun hn => hn (hiff.mpr hn)) (fun hp => hiff.mp hp hp)

end MLTStar.Design
