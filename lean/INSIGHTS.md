# What the Lean encoding showed

Notes on what came out of encoding MLT* in Lean 4 that was not visible from
`mlt_star.als` or `tptp/mlt-star.p`. Every figure here is produced by
`scripts/AxiomAudit.lean`, which walks proof terms rather than statements, and
every claim is a theorem in `MLTStar/`. `derivation-graph.html` draws the same
data as a graph.

Counts are over the **114** named results in `MLTStar/`, and "reaches an axiom"
means the result's proof term mentions that axiom transitively.

| Rests on | Results |
| --- | --- |
| nothing — the definitions alone | 54 |
| `a13`–`a15` constants | 39 |
| `a9` extensionality | 10 |
| `a4` grounding | 6 |
| `a9` and `a13`–`a15` | 5 |

---

## 1. Most of the axiomatisation is not axioms

`tptp/mlt-star.p` has 23 axioms and 10 conjectures. Sorted by what they turn
into:

| | Count | |
| --- | --- | --- |
| Become Lean `def`s | 12 | `a2`, `a3`, `a5`–`a8`, `a10`–`a12`, and the complete/disjoint categorization and partitioning definitions |
| Become unnecessary | 5 | `singleton`, `unions`, `setidentity`, `membershiptyping`, `setsareindividuals` |
| Discharged by the encoding | 1 | `a1` — the domain of quantification *is* a type |
| Survive as assumptions | 5 | `a4`, `a9`, `a13`, `a14`, `a15` |

The twelve definitional axioms are biconditionals introducing a new predicate
from existing ones. As Lean `def`s they are conservative extensions: they
cannot introduce inconsistency, and the corresponding TPTP biconditionals hold
by `Iff.rfl`. First-order logic cannot mark that distinction — an axiom is an
axiom — so the file reads as a far larger commitment than it is.

What you actually have to trust is three things, kept in three classes so that
each theorem's hypotheses record which it uses: `Extensional`, `Grounded`,
`Constants`.

## 2. `a4` costs six formulae and buys nothing the file asks for

Six of 114 results reach `a4`, and **not one is a conjecture of the TPTP
file**. Five are substantive; the sixth, `MLTStar.grounded`, is the axiom's own
restatement.

* `exists_individual_reachable`
* `not_all_instances_specialize`
* `not_categorizes_self`
* `IsPowertypeOf.ne`
* `Categorizes.ne`

Meanwhile `a4` is the sole reason for the auxiliary theory of sets of types.
Six of the file's 23 axioms — `a4` and its five scaffolding axioms — exist to
state something no conjecture uses.

The axiom does earn its place, elsewhere. Quantifying over predicates rather
than over encoded finite sets makes it one line, and in that form it *derives*
the `typeWellFounded` fact that `mlt_star.als` has to assume separately. Two
assumptions collapse into one.

Its whole yield rests on a single lemma:

> **`not_all_instances_specialize`** — no type has all of its instances
> specializing it.

Such a type would be self-supporting: an instance of an instance of `t` would
again be an instance of `t`, so the class of `t`'s instances would be closed
under instantiation, which is exactly what `a4` forbids. Two shapes of
circularity follow, neither previously recorded: no type is its own Cardelli
powertype (`IsPowertypeOf.ne`), and no type categorizes itself
(`not_categorizes_self`).

## 3. The constants are the load-bearing axiom

`a13`–`a15` reads like notational convenience. It is the widest-reaching
assumption in the theory: 44 of 114 results, against 15 for extensionality and
6 for grounding.

It also has ontological force that had not been drawn out.

> **`exists_individual`** — the mere existence of `cIndividual` forces an
> individual to exist.

If nothing were an individual, nothing would instantiate `cIndividual`; having
no instances, `cIndividual` would itself be an individual — a contradiction.
MLT* cannot be satisfied by a domain of pure types, and this follows from `a13`
with no help from `a4`.

That one forced individual then forces the whole chain
`cIndividual : cFot : cSot`, all three provably distinct
(`iof_cIndividual_cFot`, `iof_cFot_cSot`, `cIndividual_ne_cFot` and siblings).

## 4. The constants *are* the stratification

`cFot` is not merely *a* Cardelli powertype of `cIndividual` — it is *the* one
(`IsPowertypeOf.eq_cFot`), and likewise `cSot` of `cFot`. More strongly:

> **`firstOrderType_iff_specializes_cIndividual`** — being first-order is the
> same condition as specializing `cIndividual`.

with `secondOrderType_iff_specializes_cFot` its analogue. The constants are the
tops of their orders, and `cIndividual_basicType`, `cFot_basicType`,
`cSot_basicType` show they are the first three basic types of `mlt_star.als`.

What climbs the stratification is the powertype, and it climbs by exactly one:

> **`IsPowertypeOf.secondOrderType`** — the Cardelli powertype of a first-order
> type is a *second*-order type.

`powertypeNotFirstOrder` in the TPTP file is the weak shadow of this: it says
only that the powertype is not first-order, not what it is. Underneath sits
`firstOrderType_of_specializes` — order is inherited *downwards* along
specialization — from which specialization provably never crosses orders in
either direction.

## 5. The negative results are as informative as the positive ones

Three things that cannot be proved, each for a reason worth knowing.

**Subordination is not provably irreflexive.** `a4` constrains instantiation
descending, not proper specialization ascending; an infinite strictly ascending
chain of instances satisfies it. If irreflexivity is wanted it needs
stratification or a further axiom.

**`iof` is not provably irreflexive — and should not be.** A universal type
instantiates itself (`IsUniversal.iof_self`). What is elegant is that `a4` is
precisely the weakest well-foundedness condition compatible with that: it
permits self-instantiation at the top while still forcing every type to bottom
out in individuals. A blunter acyclicity axiom would break MLT*.

**The star content is permissive, not mandatory.** The four-element model
contains no universal type and no orderless type at all (`Model.no_universal`,
`Model.no_orderless`). The axioms therefore do not *entail* the phenomena MLT*
was extended to accommodate; they permit them. Establishing that requires
exhibiting a model, which is why it appears in neither existing specification.

## 6. A third formalisation is a differential test on the first two

Both defects found in `tptp/mlt-star.p` surfaced the same way: transcribing
forces a decision the original never had to make.

`a12_subordinationDef` quantified `T4` universally where the paper and
`mlt_star.als` quantify existentially. The error was invisible **because** no
conjecture mentioned subordination — nothing exercised it, so no prover ever
disagreed. It matters: under the universal reading any two instances of `T2`
must share an instance, so a `T2` that disjointly categorizes anything can have
at most one instance.

The formulae of `t1_basetypeUnique` and `t2_powertypeUnique` were interchanged
with respect to their names and comments. That survived because both are true,
so both reports came back green.

Both are now corrected in `tptp/mlt-star.p`.

The methodological point generalises. Because the axioms are typeclasses rather
than global assumptions, a theorem can only use an axiom it names in its own
hypotheses, and `scripts/AxiomAudit.lean` turns "which axioms does this really
need" into a command. Claims like *no conjecture needs `a4`* stop being
editorial and become checkable — and stay checkable as the theory grows.

## 7. `a13`–`a15` is bounded closure in disguise

The constants look like notational convenience, then like an existence axiom
(§3). They are really neither. `Experiments/NoConstants.lean` separates the two
jobs `Constants` does — a **seed** (a type of all individuals exists) and a
**successor** (basic types have powertypes) — and the second is where the design
decision lives.

Left unbounded, the successor forces an infinite domain: the tower of basic
types is injective (`tower_injective`), so `Nat` embeds. Bounded at height `h`,
finite models return. And the bounded version is not new:

> `Stratified D 2` and `Constants D` prove each other.

`a13`–`a15` *is* bounded closure at height two, written out as three constants
rather than as a schema. That is why the four-element model of
`MLTStar/Model.lean` exists at all, and it locates the real choice in the theory:
fix a height and keep finite models, or let the tower run and lose them. Nothing
else depends on the answer — the unbounded axioms prove `Constants`, so every
theorem in `MLTStar/` holds either way.

A corollary worth stating, because the question arises naturally: **no axiom one
could add restores a finite model.** Adding axioms removes models and never adds
any, so every extension of the unbounded theory still proves `nat_embeds`,
inconsistent extensions included. The successor axiom has to be weakened, not
supplemented.

## 8. Two results the existing specifications state only halves of

> **`categorizes_iff`** — the categorizers of `t` are *exactly* the
> specializations of the Cardelli powertype of `t` that do not have `t` itself
> as an instance.

`t4` is one half of one direction of this.

> **`Partitions.existsUnique`** — every instance of the base type instantiates
> *exactly one* instance of a type that partitions it.

Completeness supplies at least one and disjointness at most one. Both
specifications state the two halves and never draw the conclusion the name has
always promised. Neither result needs any axiom.

---

## 9. Alternative designs

`Experiments/Designs.lean` tests three changes one might want to make. All of
the following are proved there.

### Specialization belongs on the types

On the full domain `Specializes` is not even reflexive — an individual
specializes nothing, itself included (`not_specializes_self_of_individual`). On
the subtype of types it is reflexive, transitive and antisymmetric: a partial
order. That is a presentational change with no logical cost, and it is what lets
the next point be stated cleanly.

### The powertype is an order embedding, not merely monotone

`t3` says the powertype *preserves* specialization. It also **reflects** it:

> `specializes_powertype_iff` — `℘t₁ ⊑ ℘t₂ ↔ t₁ ⊑ t₂`.

The proof is two lines, because a base type instantiates its own powertype, so
`℘t₁ ⊑ ℘t₂` applied at `t₁` already yields `t₁ ⊑ t₂`. No axiom is needed.

This is the most promising direction for a more elegant MLT*. Together with §7,
the stratification is the orbit of a single operator on a poset:

| MLT* as stated | MLT* as an operator |
| --- | --- |
| `a10` + `t1` | `℘` is a well-defined function on types |
| `t2` | `℘` is injective |
| `t3` | `℘` is monotone — and in fact an order embedding |
| `IsPowertypeOf.ne` | `℘` has no fixed point |
| `a13`–`a15` | the tower `℘ⁿ(⊥)` exists up to height 2 |

So: *a poset of types with a bottom element and an injective, fixed-point-free
order embedding on it, whose orbit from the bottom is the ordered types.*
Everything else — orders, basic types, orderless types — is derived. That is a
much smaller thing to state than the present axiom list, and `powertype_injective`
shows `t2` falls straight out of the embedding property rather than needing its
own argument.

### The axioms are independent

Neither `a9` nor `a4` follows from the rest, so nothing is redundant:

* `extensional_independent` — a five-element model of `a4` and the constants with
  two distinct coextensive types. `Constants` asks only that *some* type has
  exactly the individuals as instances; with `a9` gone, nothing makes it unique.
* `grounded_independent` — the four-element model plus a self-supporting type `u`
  whose only instance is itself. Extensionality and the constants survive
  untouched, since `u` is neither first- nor second-order; but `{u}` is a
  non-empty class of types closed under instantiation.

With `Collapse` from `NoConstants.lean` — a model of `a9` and `a4` with no type
of individuals — all three are pairwise independent.

## 10. Why the theory can afford only the powertype

MLT* is ungenerous about which types exist: the constants, and powertypes. That
turns out to be forced.

* `no_comprehension` — "every class of entities is the extension of some type" is
  inconsistent outright. Russell's argument goes through verbatim on
  instantiation: take the class of entities that do not instantiate themselves.
* `no_separation_with_universal` — the standard repair fails too. Separation,
  carving a type out of the instances of an existing type, reproduces the
  contradiction as soon as a universal type exists.

And a universal type is precisely what MLT* was extended to admit (§5). So the
theory cannot have comprehension *or* separation.

It does not follow that the theory can have no type-forming operations at all —
see §13, which corrects an over-reach in an earlier version of this section.
Comprehension is unbounded; a *binary union* is not, and the two fail for quite
different reasons, or in the case of union do not fail.

## 11. Subordination is bounded by finiteness, not by order

§5 left `IsSubordinateTo t t` unrefuted and guessed that restricting to *ordered*
types would fix it. `Experiments/Subordination.lean` settles it, and the guess
was wrong.

Unfolded, self-subordination says exactly that the instances of `t` have **no
maximal element** under proper specialization (`isSubordinateTo_self_iff`). So
irreflexivity is an *ascending* chain condition — which is why `a4`, a
*descending* condition on instantiation, cannot deliver it, and why being
ordered does not either: orderedness says nothing about ascending chains.

What does bound it is finiteness. A self-subordinate type generates a strictly
ascending chain of its own instances, and proper specialization is transitive
and irreflexive, so the chain never repeats:

> `nat_embeds_of_self_subordinate` — a type subordinate to itself embeds `Nat`
> into its own instances.

Hence subordination is irreflexive in every finite model, `Model.not_isSubordinateTo_self`
being the concrete case, and any counterexample must be infinite. If irreflexivity
is wanted outright, the axiom to add is an ascending chain condition on proper
specialization — not a restriction to ordered types.

## 12. The powertype does have an adjoint

`categorizes_iff` (§8) reads like half a Galois connection, and it is one. The
lower adjoint is "union of instances":

> `IsUnionOf u p` — `u` collects the instances of the instances of `p`.

Two results in `Experiments/Designs.lean` §6. `union_powertype`: the union of
`℘t` is `t`, so union inverts the powertype on its image. And the adjunction law
itself, for arbitrary `p` and `t`:

> `union_specializes_iff` — `L p ⊑ t ↔ p ⊑ ℘ t`.

Neither needs an axiom. So `℘` is a right adjoint, and the Odell/Cardelli
relationship is structural after all.

The reason MLT* does not *look* like it has an adjunction is that it cannot
guarantee the unions exist — by §10 it has no comprehension to build them with.
The adjoint is definable pointwise wherever the union happens to be there, and
nowhere else. That is the same absence that keeps the poset of types from being
a lattice, seen from another side.

## 13. Union is not comprehension, and type existence is the real gap

An earlier version of §10 said the types have no meets or joins "since that
would need exactly the comprehension the theory cannot have". That is wrong, and
the mistake is worth keeping because the correction is the most interesting thing
in this document.

**The base theory says almost nothing about which types exist.** `IsPowertypeOf`
is a *defined relation* and is nowhere asserted to be inhabited, so the only
types MLT* claims outright are the three constants. Every other result is
conditional: *if* such types exist, then… That is the real gap, and comprehension
was a red herring for it.

**Joins are fine.** A binary union names no predicate the theory lacked
extensions for; it is bounded, and Russell's argument does not touch it. Adding
it makes the types a join-semilattice — `IsJoinOf.le_left`, `.le_right` and
`.least` show the union is genuinely the least upper bound in the specialization
order — and `Pair.consistent` gives a model, so union closure is not
self-defeating the way comprehension is.

**Meets fail for an unrelated reason.** MLT* *defines* `Individual x` as "`x` has
no instances". An entity with empty extension is therefore an individual, not an
empty type: `no_empty_type`. Two types with disjoint extensions consequently have
no meet (`no_meet_of_disjoint`), and this is not an edge case —
`no_meet_of_disjointlyCategorizes` shows it bites exactly where MLT*'s own
partitioning notion applies, since the instances of a disjoint categorizer are
pairwise disjoint by construction. So the obstruction is the individual/type
dichotomy, not comprehension.

**And union closure earns its keep.** It is not merely harmless:

> `exists_orderlessType` — with the constants and binary unions, an orderless
> type must exist.

The type of all individuals has an individual among its instances; the type of
all first-order types has `cIndividual`, a *type*, among its instances. Their
union has both, and a type with both an individual and a type among its
instances can specialize no basic type (`not_orderedType_of_mixed`: a basic type
is either the type of all individuals, whose instances are all individuals, or a
powertype, whose instances are all types — so neither can be specialized by
something mixed).

This is the best answer this development has to where orderless types come from.
`Model.no_orderless` shows the base axioms merely *permit* them; a single bounded
existence principle *forces* them. Basic MLT plus binary unions is MLT*.

What union does not give is the constants: `cIndividual` collects all
individuals, an infinitary union that no iteration of a binary one reaches. So
there are two independent existence principles in play — unions generate
orderless types from types already present, the constants supply the ordered
ones — and the theory currently states only the second.

## 14. Singletons: the third existence principle

The natural candidate for what MLT* is missing, and the one with an ontological
reading the others lack — **every entity has a type**. Without it the theory
permits entities that nothing classifies: `cSot` is an instance of nothing in the
four-element model.

Adding it (`SingletonClosed`) settles several things at once.

**It classifies everything, and separates points.** `exists_type_of` is
immediate, and `sing_inj` — distinct entities have distinct singletons — needs no
extensionality, since `x` instantiates its own singleton.

**But it does not generate orderless types.** This is the sharp contrast with
union, and it is the answer to whether singletons are the missing piece for §13:

> `orderedType_sing_iff` — `sing x` is ordered exactly when `x` instantiates some
> basic type. Hence `orderlessType_sing`: the singleton of an orderless type is
> orderless, and the singleton of anything ordered is ordered.

Singletons *propagate* the star phenomena and never introduce them. Union
introduces them and cannot separate points. The two principles do genuinely
different work.

**It costs an infinite domain.** Iterating on an individual gives a chain that
never repeats (`nat_embeds_of_singletonClosed`), for the same reason unbounded
powertype closure does.

**Together with union it gives finite comprehension.** Singleton supplies the
points, union the gluing, so every finite non-empty class of entities is realised
as a type — `exists_pairType` is the two-element case. Finite comprehension is
bounded, so §10's Russell argument does not touch it. This is where the
generative power sits.

**The three are independent.** Each of the models already in the development
separates them:

| Model | singleton | union | constants |
| --- | --- | --- | --- |
| `Chain` (the naturals) | yes | no (`not_unionClosed`) | — |
| `Pair` | no (`not_singletonClosed`) | yes | — |
| `Model.W` (four elements) | no (`not_singletonClosed`) | no | yes |

`Chain` is singleton-closed for a pleasing reason: `sing ⟨n⟩ = ⟨n+1⟩`, so in that
model the singleton *is* the successor, and is also the Cardelli powertype.

**So the answer to "is singleton the missing principle" is: it is one of three,
and not the one that explains orderless types.** The existence story that emerges
has three independent posits — singleton for classification, union for
orderlessness, and the constants for the infinitary collections neither can
reach — where the theory as published states only the third.

## What could be proved next

Open, in rough order of how much they would clarify:

1. **A characterisation of orderless types.** A universal type is orderless; is
   the converse-ish statement provable — that an orderless type must have
   instances at two or more orders? That would turn "orderless" from a negative
   definition into a positive one.
2. **Models at each height.** `Stratified D h` has finite models. Are they
   classified by their individuals plus a choice of which specializations exist,
   or is there more freedom?
3. **Decidability of the ordered fragment.** Basic MLT — everything ordered, no
   orderless types — looks like it might be decidable, where full MLT* very
   likely is not.
4. **Whether the ascending chain condition of §11 has a natural axiomatisation**
   — one that does not simply assert finiteness.

## Reproducing the figures

```sh
cd lean
lake build
LEAN_PATH=.lake/build/lib/lean lean scripts/AxiomAudit.lean
```

One tab-separated row per declaration: kind, whether it was hand-written,
name, axioms reached, dependencies within `MLTStar`. The counts above are the
`thm` + `src` rows.
