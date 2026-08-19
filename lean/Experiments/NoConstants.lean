import MLTStar

/-!
# Experiment: MLT* without the constants

The main development takes `a13`–`a15` as primitive: `Constants` supplies
`cIndividual`, `cFot` and `cSot` outright. The audit shows this is the
load-bearing axiom — 44 of 114 results reach it — so it is worth asking what
would have to replace it if we still wanted ordered types, and basic types as
their topmost types.

This file is an experiment. Nothing in `MLTStar/` imports it.

## The question

Removing `Constants` costs two things at once, and they are worth separating:

1. a **seed** — that a type of all individuals exists at all;
2. a **successor** — that the tower of basic types keeps going.

`Constants` bundles the seed with the first two steps of the tower, which is
why it looks like mere notation and behaves like an existence axiom. Section 1
shows what happens with neither: the stratification collapses entirely. The
replacement proposed here is `Seeded` plus `BasicPowertypeClosed`, one axiom for
each job.

## What comes out

* `Seeded` alone recovers `cIndividual` as a *definition*, unique up to `a9`.
* `Seeded` + `BasicPowertypeClosed` generate the whole tower `tower : Nat → E`,
  which is injective (`tower_injective`) — so this axiomatisation forces an
  infinite domain, where `Constants` is satisfied by four elements.
* The two together **prove** `Constants` (`constantsOfTower`), so the
  alternative is strictly stronger and everything in `MLTStar/` transfers.
* `Constants` does *not* prove the closure (`Model.no_powertype_of_cSot`), so
  the strengthening is real.

Two things also turn out **not** to need replacing. `a4` already gives what was
being read off `a13`: on a non-empty domain, grounding alone forces an
individual to exist (`exists_individual_of_grounded`). And the seed is enough
for order one on its own; only the tower above it needs the successor axiom.
-/

namespace MLTStar.Experiment

universe u
variable {E : Type u} [Domain E]

/-! ## 1. With neither axiom, every type is orderless

A three-element domain: two individuals and a type that has only one of them as
an instance. It satisfies `a9` and `a4`, but no type has *exactly* the
individuals as its instances, so `BasicType` is empty — and with it
`OrderedType`. The stratification does not merely lose its bottom; it vanishes.
-/

namespace Collapse

inductive V where
  | i₁ | i₂ | t
  deriving DecidableEq, Repr

/-- `i₁` is an instance of `t`; `i₂` is an instance of nothing. -/
def viof (a b : V) : Prop := a = .i₁ ∧ b = .t

instance : Domain V := ⟨viof⟩

instance instDecidableViof (a b : V) : Decidable (viof a b) := by
  unfold viof; infer_instance

instance (a b : V) : Decidable (iof a b) := inferInstanceAs (Decidable (viof a b))

instance instDecidableForallV (p : V → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p .i₁ ∧ p .i₂ ∧ p .t)
    ⟨fun h x => by cases x <;> simp_all, fun h => ⟨h _, h _, h _⟩⟩

instance instDecidableExistsV (p : V → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  decidable_of_iff (p .i₁ ∨ p .i₂ ∨ p .t)
    ⟨fun h => by rcases h with h | h | h <;> exact ⟨_, h⟩,
     fun ⟨x, hx⟩ => by cases x <;> simp_all⟩

instance (x : V) : Decidable (IsType x) := inferInstanceAs (Decidable (∃ y, iof y x))
instance (x : V) : Decidable (Individual x) := inferInstanceAs (Decidable (¬ ∃ y, iof y x))

theorem not_isType_i₁ : ¬ IsType V.i₁ := by decide
theorem not_isType_i₂ : ¬ IsType V.i₂ := by decide

instance : Extensional V where
  typeExtensionality := by decide

instance : Grounded V where
  grounded S hne hty := by
    by_cases h : S .t
    · exact ⟨.t, h, .i₁, by decide, fun hs => not_isType_i₁ (hty _ hs)⟩
    · obtain ⟨y, hy⟩ := hne
      cases y
      · exact absurd (hty _ hy) not_isType_i₁
      · exact absurd (hty _ hy) not_isType_i₂
      · exact absurd hy h

/-- No type has exactly the individuals as its instances: `i₂` is an individual
that instantiates nothing. -/
theorem no_individualType : ¬ ∃ b : V, ∀ e, iof e b ↔ Individual e := by decide

/-- Hence there are no basic types at all. -/
theorem no_basicType : ¬ ∃ b : V, BasicType b := by
  rintro ⟨b, hb⟩
  induction hb with
  | individuals h => exact no_individualType ⟨_, h⟩
  | powertype _ _ ih => exact ih

/-- Hence no ordered types, and every type is orderless. -/
theorem no_orderedType : ¬ ∃ t : V, OrderedType t :=
  fun ⟨_, b, hb, _⟩ => no_basicType ⟨b, hb⟩

theorem all_types_orderless : ∀ t : V, IsType t → OrderlessType t :=
  fun _ ht => ⟨ht, fun ho => no_orderedType ⟨_, ho⟩⟩

end Collapse

/-! ## 2. What `a4` already gives

`exists_individual` is proved in `MLTStar/Constants.lean` from `a13`. It does
not need it: grounding alone forces an individual on any non-empty domain, since
otherwise the class of *all* entities would be a non-empty class of types closed
under instantiation. So this much survives the removal untouched. -/

theorem exists_individual_of_grounded [Grounded E] [Nonempty E] : ∃ x : E, Individual x := by
  apply Classical.byContradiction
  intro hno
  have hall : ∀ x : E, IsType x := fun x =>
    Classical.byContradiction fun h => hno ⟨x, h⟩
  obtain ⟨-, -, -, -, hzn⟩ :=
    grounded (fun _ : E => True) ⟨Classical.choice inferInstance, trivial⟩ (fun y _ => hall y)
  exact hzn trivial

/-! ## 3. The seed

The weakest thing that can replace the *existence* half of `a13`: a type whose
instances are exactly the individuals. Unlike `Constants` it names nothing — the
constant becomes a definition, and `a9` makes it unique. -/

/-- There is a type of all individuals. -/
class Seeded (E : Type u) [Domain E] : Prop where
  exists_individualType : ∃ b : E, ∀ e, iof e b ↔ Individual e

instance [Seeded E] : Nonempty E := ⟨Seeded.exists_individualType.choose⟩

/-- The type of all individuals, recovered as a definition rather than assumed
as a constant. -/
noncomputable def individualType (E : Type u) [Domain E] [Seeded E] : E :=
  Seeded.exists_individualType.choose

theorem iof_individualType_iff [Seeded E] (e : E) :
    iof e (individualType E) ↔ Individual e :=
  Seeded.exists_individualType.choose_spec e

/-- Any type of all individuals is *the* type of all individuals. This is what
`a9` buys once the constant is no longer primitive. -/
theorem eq_individualType [Extensional E] [Grounded E] [Seeded E] {b : E}
    (h : ∀ e, iof e b ↔ Individual e) : b = individualType E := by
  obtain ⟨i, hi⟩ := exists_individual_of_grounded (E := E)
  exact typeExtensionality ⟨i, (h i).mpr hi⟩ ⟨i, (iof_individualType_iff i).mpr hi⟩
    fun x => (h x).trans (iof_individualType_iff x).symm

theorem individualType_isType [Grounded E] [Seeded E] : IsType (individualType E) := by
  obtain ⟨i, hi⟩ := exists_individual_of_grounded (E := E)
  exact ⟨i, (iof_individualType_iff i).mpr hi⟩

theorem individualType_basicType [Seeded E] : BasicType (individualType E) :=
  .individuals iof_individualType_iff

/-- The order-one characterisation survives verbatim: being first-order is the
same condition as specializing the seed. -/
theorem firstOrderType_iff_specializes [Seeded E] {t : E} :
    FirstOrderType t ↔ Specializes t (individualType E) :=
  ⟨fun h => ⟨h.1, fun e he => (iof_individualType_iff e).mpr (h.2 e he)⟩,
   fun h => ⟨h.1, fun e he => (iof_individualType_iff e).mp (h.2 e he)⟩⟩

/-- Basic types are types. In `MLTStar/Stratification.lean` this needs
`Constants`; here the seed and `a4` suffice. -/
theorem basicType_isType [Grounded E] [Seeded E] {b : E} (h : BasicType b) : IsType b := by
  cases h with
  | individuals hb =>
      obtain ⟨i, hi⟩ := exists_individual_of_grounded (E := E)
      exact ⟨i, (hb i).mpr hi⟩
  | powertype _ hp => exact hp.isType_left

/-! ## 4. The successor

The seed gives order one and stops. What carries the stratification upwards is
that each basic type has a Cardelli powertype — which is then basic in turn. -/

/-- Every basic type has a Cardelli powertype. -/
class BasicPowertypeClosed (E : Type u) [Domain E] : Prop where
  exists_powertype : ∀ b : E, BasicType b → ∃ p, IsPowertypeOf p b

variable [Seeded E] [BasicPowertypeClosed E]

/-- One step up the tower. -/
noncomputable def nextBasic (b : {x : E // BasicType x}) : {x : E // BasicType x} :=
  ⟨(BasicPowertypeClosed.exists_powertype b.1 b.2).choose,
   .powertype b.2 (BasicPowertypeClosed.exists_powertype b.1 b.2).choose_spec⟩

theorem nextBasic_isPowertypeOf (b : {x : E // BasicType x}) :
    IsPowertypeOf (nextBasic b).1 b.1 :=
  (BasicPowertypeClosed.exists_powertype b.1 b.2).choose_spec

noncomputable def towerAux : Nat → {x : E // BasicType x}
  | 0 => ⟨individualType E, individualType_basicType⟩
  | n + 1 => nextBasic (towerAux n)

/-- The tower of basic types: `tower 0` is the type of all individuals, and each
step is the Cardelli powertype of the one below. -/
noncomputable def tower (n : Nat) : E := (towerAux (E := E) n).1

theorem tower_basicType (n : Nat) : BasicType (tower (E := E) n) := (towerAux n).2

theorem tower_zero : tower (E := E) 0 = individualType E := rfl

theorem tower_isPowertypeOf (n : Nat) :
    IsPowertypeOf (tower (E := E) (n + 1)) (tower (E := E) n) :=
  nextBasic_isPowertypeOf (towerAux n)

theorem tower_orderedType [Grounded E] (n : Nat) : OrderedType (tower (E := E) n) :=
  ⟨_, tower_basicType n, Specializes.refl (basicType_isType (tower_basicType n))⟩

/-! ### The cost: the domain must be infinite -/

theorem tower_zero_ne_succ [Grounded E] (k : Nat) :
    tower (E := E) 0 ≠ tower (E := E) (k + 1) := by
  intro heq
  have hbase : iof (tower (E := E) k) (tower (E := E) (k + 1)) :=
    (tower_isPowertypeOf k).iof_base
  have : Individual (tower (E := E) k) :=
    (iof_individualType_iff _).mp (by rw [← tower_zero, heq]; exact hbase)
  exact this (basicType_isType (tower_basicType k))

theorem tower_injective [Extensional E] [Grounded E] :
    ∀ m n : Nat, tower (E := E) m = tower (E := E) n → m = n := by
  intro m
  induction m with
  | zero => intro n h; cases n with
    | zero => rfl
    | succ k => exact absurd h (tower_zero_ne_succ k)
  | succ j ih => intro n h; cases n with
    | zero => exact absurd h.symm (tower_zero_ne_succ j)
    | succ k =>
        -- one powertype, two base types: `t2` makes the base unique
        have hbase : tower (E := E) k = tower (E := E) j :=
          Classical.byContradiction fun hne =>
            t2_powertypeUnique (tower_isPowertypeOf j)
              ⟨tower k, fun he => hne he, h ▸ tower_isPowertypeOf k⟩
        exact congrArg Nat.succ (ih k hbase.symm)

/-! ## 5. The seed and the successor prove `a13`–`a15`

`cIndividual`, `cFot` and `cSot` are the first three rungs. So the alternative
axiomatisation is at least as strong as the present one, and every theorem in
`MLTStar/` holds under it. -/

theorem secondOrderType_iff_specializes_tower_one [Grounded E] {t : E} :
    SecondOrderType t ↔ Specializes t (tower (E := E) 1) := by
  constructor
  · exact fun h => ⟨h.1, fun e he =>
      ((tower_isPowertypeOf 0).2 e).mpr (firstOrderType_iff_specializes.mp (h.2 e he))⟩
  · exact fun h => ⟨h.1, fun e he =>
      firstOrderType_iff_specializes.mpr (((tower_isPowertypeOf 0).2 e).mp (h.2 e he))⟩

/-- The present axiomatisation, derived. Deliberately a `def` rather than an
`instance`: it is a result about the experiment, not something to fire during
elaboration of the main development. -/
noncomputable def constantsOfTower [Grounded E] : Constants E where
  cIndividual := tower 0
  cFot := tower 1
  cSot := tower 2
  cIndividual_spec := iof_individualType_iff
  cFot_spec := fun x =>
    ((tower_isPowertypeOf 0).2 x).trans firstOrderType_iff_specializes.symm
  cSot_spec := fun x =>
    ((tower_isPowertypeOf 1).2 x).trans secondOrderType_iff_specializes_tower_one.symm

/-! ## 6. The alternative is consistent

`tower_injective` rules out any finite model, so the four-element model of
`MLTStar/Model.lean` cannot witness consistency here. This one can: the natural
numbers, where each level has the one below it as its sole instance.

```
    ⟨0⟩ : ⟨1⟩ : ⟨2⟩ : ⟨3⟩ : …
```

`⟨0⟩` is the only individual, `⟨1⟩` is the type of all individuals, and `⟨n+1⟩`
is the Cardelli powertype of `⟨n⟩`. It satisfies `a9`, `a4`, `Seeded` and — in
the stronger form, for *every* type rather than every basic type — powertype
closure.
-/

namespace Chain

/-- A level of the chain. -/
structure Lvl where
  n : Nat
  deriving DecidableEq

/-- `a` is an instance of `b` exactly when `b` is one level up. -/
instance : Domain Lvl := ⟨fun a b => b.n = a.n + 1⟩

theorem iof_iff {a b : Lvl} : iof a b ↔ b.n = a.n + 1 := Iff.rfl

theorem eq_of_n {a b : Lvl} (h : a.n = b.n) : a = b := congrArg Lvl.mk h

theorem individual_iff {x : Lvl} : Individual x ↔ x.n = 0 := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hne
    exact h ⟨⟨x.n - 1⟩, iof_iff.mpr (show x.n = (x.n - 1) + 1 by omega)⟩
  · intro hx h
    obtain ⟨y, hy⟩ := h
    rw [iof_iff, hx] at hy
    omega

theorem isType_iff {x : Lvl} : IsType x ↔ 0 < x.n := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := h
    rw [iof_iff] at hy
    omega
  · intro h
    exact ⟨⟨x.n - 1⟩, iof_iff.mpr (show x.n = (x.n - 1) + 1 by omega)⟩

instance : Extensional Lvl where
  typeExtensionality t₁ t₂ h₁ _ h := by
    have hpos : 0 < t₁.n := isType_iff.mp h₁
    have hstep : iof ⟨t₁.n - 1⟩ t₁ :=
      iof_iff.mpr (show t₁.n = (t₁.n - 1) + 1 by omega)
    have h2 : t₂.n = (t₁.n - 1) + 1 := iof_iff.mp ((h _).mp hstep)
    exact eq_of_n (by omega)

/-- Least-element principle. `Nat.find` lives in Mathlib, so this is proved here
by ordinary induction on a bound. -/
theorem exists_least (S : Nat → Prop) :
    ∀ bound k, S k → k ≤ bound → ∃ m, S m ∧ ∀ j, j < m → ¬ S j := by
  intro bound
  induction bound with
  | zero => exact fun k hk hle => ⟨k, hk, fun j hj => absurd hj (by omega)⟩
  | succ b ih =>
      intro k hk hle
      by_cases hlt : ∃ j, j < k ∧ S j
      · obtain ⟨j, hjk, hj⟩ := hlt
        exact ih j hj (by omega)
      · exact ⟨k, hk, fun j hj hsj => hlt ⟨j, hj, hsj⟩⟩

instance : Grounded Lvl where
  grounded S hne hty := by
    classical
    obtain ⟨y₀, hy₀⟩ := hne
    obtain ⟨m, hm, hmin⟩ :=
      exists_least (fun k => S ⟨k⟩) y₀.n y₀.n hy₀ (Nat.le_refl _)
    have hpos : 0 < m := isType_iff.mp (hty _ hm)
    exact ⟨⟨m⟩, hm, ⟨m - 1⟩, iof_iff.mpr (show m = (m - 1) + 1 by omega),
      hmin (m - 1) (by omega)⟩

instance : Seeded Lvl where
  exists_individualType := ⟨⟨1⟩, fun e => by
    have h1 : iof e (⟨1⟩ : Lvl) ↔ (1 : Nat) = e.n + 1 := Iff.rfl
    rw [h1, individual_iff]
    constructor <;> intro h <;> omega⟩

/-- Every type has a Cardelli powertype — the level above it. This is stronger
than `BasicPowertypeClosed`, which asks it only of basic types. -/
theorem exists_powertype (t : Lvl) (ht : IsType t) : ∃ p, IsPowertypeOf p t := by
  refine ⟨⟨t.n + 1⟩, ⟨⟨t, iof_iff.mpr rfl⟩, fun x => ?_⟩⟩
  constructor
  · intro hx
    have hstep : t.n + 1 = x.n + 1 := iof_iff.mp hx
    have hxt : x = t := eq_of_n (by omega)
    subst hxt
    exact Specializes.refl ht
  · intro hs
    have hpos : 0 < x.n := isType_iff.mp hs.1
    have hxt : t.n = (x.n - 1) + 1 :=
      iof_iff.mp (hs.2 ⟨x.n - 1⟩ (iof_iff.mpr (show x.n = (x.n - 1) + 1 by omega)))
    exact iof_iff.mpr (show t.n + 1 = x.n + 1 by omega)

instance : BasicPowertypeClosed Lvl where
  exists_powertype b hb := exists_powertype b (basicType_isType hb)

/-- So the alternative axiomatisation is consistent. -/
theorem consistent :
    ∃ (E : Type) (_ : Domain E) (_ : Extensional E) (_ : Grounded E) (_ : Seeded E),
      Nonempty (BasicPowertypeClosed E) :=
  ⟨Lvl, inferInstance, inferInstance, inferInstance, inferInstance, ⟨inferInstance⟩⟩

end Chain


/-! ## 8. No *added* axiom can restore a finite model

Adding axioms removes models; it never adds any. `Seeded` together with
`BasicPowertypeClosed` already proves that `Nat` embeds into the domain, so
every extension of that theory proves it too — including an inconsistent one,
which has no models at all. The question "what axiom would give us a finite
model" therefore has no answer of that shape: the successor axiom has to be
*weakened*, not supplemented.

The natural weakening is to bound the height of the tower rather than let it
climb forever. -/

/-- `Seeded` + `BasicPowertypeClosed` embed `Nat` in the domain, so no model of
theirs is finite — and no further axiom can change that. -/
theorem nat_embeds [Extensional E] [Grounded E] :
    ∃ f : Nat → E, ∀ m n, f m = f n → m = n :=
  ⟨tower, tower_injective⟩

/-! ## 9. Bounded closure — and `a13`–`a15` is exactly its height-2 case

`Stratified D h` says the tower exists and climbs `h` times. Nothing then forces
it to climb further, so finite models are permitted again.

The punchline is that this is not a new axiom at all: `Stratified D 2` and
`Constants D` prove each other. The present encoding was already the bounded
one — `a13`–`a15` is bounded closure at height two, written out as three
constants rather than as a schema. -/

/-- There is a tower of basic types that climbs at least `h` times. -/
class Stratified (D : Type u) [Domain D] (h : Nat) : Prop where
  exists_tower : ∃ b : Nat → D,
    (∀ e, iof e (b 0) ↔ Individual e) ∧
    (∀ n, n < h → IsPowertypeOf (b (n + 1)) (b n))

/-- Order one, relative to any type of all individuals. -/
theorem firstOrderType_iff_specializes_of {D : Type u} [Domain D] {b : D}
    (hb : ∀ e, iof e b ↔ Individual e) {t : D} : FirstOrderType t ↔ Specializes t b :=
  ⟨fun h => ⟨h.1, fun e he => (hb e).mpr (h.2 e he)⟩,
   fun h => ⟨h.1, fun e he => (hb e).mp (h.2 e he)⟩⟩

/-- Order two, relative to any type of all first-order types. -/
theorem secondOrderType_iff_specializes_of {D : Type u} [Domain D] {c : D}
    (hc : ∀ e, iof e c ↔ FirstOrderType e) {t : D} : SecondOrderType t ↔ Specializes t c :=
  ⟨fun h => ⟨h.1, fun e he => (hc e).mpr (h.2 e he)⟩,
   fun h => ⟨h.1, fun e he => (hc e).mp (h.2 e he)⟩⟩

private noncomputable def twr (D : Type u) [Domain D] [Stratified D 2] : Nat → D :=
  (Stratified.exists_tower (D := D) (h := 2)).choose

private theorem twr_zero (D : Type u) [Domain D] [Stratified D 2] :
    ∀ e : D, iof e (twr D 0) ↔ Individual e :=
  (Stratified.exists_tower (D := D) (h := 2)).choose_spec.1

private theorem twr_succ (D : Type u) [Domain D] [Stratified D 2] :
    ∀ n, n < 2 → IsPowertypeOf (twr D (n + 1)) (twr D n) :=
  (Stratified.exists_tower (D := D) (h := 2)).choose_spec.2

private theorem twr_one (D : Type u) [Domain D] [Stratified D 2] :
    ∀ e : D, iof e (twr D 1) ↔ FirstOrderType e := fun e =>
  ((twr_succ D 0 (by omega)).2 e).trans
    (firstOrderType_iff_specializes_of (twr_zero D)).symm

/-- A tower of height two gives the three constants. -/
noncomputable def constantsOfStratified (D : Type u) [Domain D] [Stratified D 2] :
    Constants D where
  cIndividual := twr D 0
  cFot := twr D 1
  cSot := twr D 2
  cIndividual_spec := twr_zero D
  cFot_spec := twr_one D
  cSot_spec := fun x =>
    ((twr_succ D 1 (by omega)).2 x).trans
      (secondOrderType_iff_specializes_of (twr_one D)).symm

/-- …and conversely, so the two are equivalent. -/
theorem stratified_of_constants (D : Type u) [Domain D] [Constants D] : Stratified D 2 where
  exists_tower :=
    ⟨fun n => match n with
      | 0 => cIndividual
      | 1 => cFot
      | _ => cSot,
     iof_cIndividual_iff,
     by
       intro n hn
       match n, hn with
       | 0, _ => exact cFot_isPowertypeOf_cIndividual
       | 1, _ => exact cSot_isPowertypeOf_cFot⟩

end MLTStar.Experiment

/-! ## 7. …and strictly stronger

The four-element model of `MLTStar/Model.lean` satisfies `Constants` but has no
powertype for `cSot`: the only specialization of `cSot` is `cSot` itself, and
nothing in the model has `cSot` as an instance. So `Constants` does not prove
`BasicPowertypeClosed`, and the extra strength is not free — by
`tower_injective` it costs an infinite domain. -/

namespace MLTStar.Model

theorem no_powertype_of_cSot : ¬ ∃ p : W, IsPowertypeOf p W.cSot := by decide

theorem not_basicPowertypeClosed : ¬ Experiment.BasicPowertypeClosed W :=
  fun h => no_powertype_of_cSot (h.exists_powertype W.cSot cSot_basicType)

/-- But it *is* a tower of height two — a finite model of the bounded axiom. -/
theorem stratified_two : Experiment.Stratified W 2 :=
  Experiment.stratified_of_constants W

end MLTStar.Model
