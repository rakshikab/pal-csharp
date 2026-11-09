# The pal-csharp translation scheme

This document defines `⟦·⟧`, the translation from annotated C# to Pulse. It is the
**specification of the emitter**: `Pal.Compiler` is an implementation of the rules below,
and anything the emitter does that is not justified by a rule here is a bug.

Every rule is **compositional**: it is defined by the shape of a C# construct alone,
independently of any example and of its surrounding context.

Rule ids (`R<section>.<n>`) are cited from `Pal.Compiler`, from the Pulse library and from
`test/`, so they are stable: a section may be reorganised, but a rule is never renumbered.
The numbering is therefore not contiguous where a rule was withdrawn. Facts (`F<n>`) are
Pulse behaviours probed and pinned in `test/pulse_facts/` before the rule that relies on
them was written; §1 lists them all.

---

## 0. The anti-contortion discipline

It is easy to write each test program directly in clean, idiomatic Pulse and then contort
the translator into producing that. The result is a pile of per-example hacks wearing a
compiler's clothes. The goal is a **translation of C#, reflecting C# semantics and
structure** — not a re-implementation of each example in Pulse.

Four rules, in force from the first commit.

**Rule 1 — Scheme before code.** This document precedes the emitter. Derived Pulse is
obtained by *hand-executing* the rules, never authored freely. Output that cannot be
justified rule-by-rule is a bug in the scheme, not a licence to tweak the output.

**Rule 2 — Structure preservation.** Emitted Pulse mirrors its source (§3–§6). Explicit
anti-goals: no inlining, no constant folding, no reordering or reassociating control flow,
no rewriting an imperative loop into a recursion or a fold, no whole-method
"recognise this algorithm" pattern matching.

**Rule 3 — The emitter never invents proof steps.** When a proof needs help, the help
comes from exactly two places:
* the user's C# annotations — `Pal.Invariant`, `Pal.Assert`, `[Lemma]` calls,
  `Pal.GhostStmt`, `Ghost<T>` arguments (this is *the point* of a proof annotation
  language); or
* general-purpose lemmas in `Pulse.Lib.CSharp.*`, usable by any program.

A special case in the emitter is never a legitimate fix.

Which library module a lemma belongs in is decided by **what it is about, not by what
motivated it**. A ring buffer wants both `Rotate(s, n)[k] == s[(n + k) % s.Length]` and
"two offsets less than a period apart have distinct residues"; the first is a fact about
sequences and belongs in `Pulse.Lib.CSharp.Seq`, the second is a fact about integers and
belongs in `Pulse.Lib.CSharp.Arith`, however much one client wanted them together. Filing
by motivation is the same mistake as rule 2's at library scale: it lets one example shape
something that is meant to be general, and leaves the next reader unable to find a fact
under the name of a data structure they are not using.

The rule reads in both directions, and the second one is easier to forget: **the frontend
never invents a refusal.** pal-csharp refuses what it cannot *translate* — a construct with
no image in Pulse, a measure it would have to guess, a field with no ownership story. What
cannot be *proved* is the prover's to say. A check that inspects a program and predicts the
proof will fail is doing separation logic in a pass that does not have it, and will
therefore be a silhouette of the rule rather than the rule: it fires on the shapes it was
written for and misses the rest. It also costs more than it looks, because a refusal hides
everything behind it — a program refused in the frontend is never emitted, so nothing else
wrong with it is ever discovered. R3.13 is the worked example; `test/pulse_refusals` is
where programs that translate faithfully and fail honestly are kept.

**Rule 3a — one question, one answer.** A refusal is *incompleteness*: it can only reject
programs that might have gone through, and rule 3 is the argument for keeping few of them.
A **duplicated analysis** is a different and worse thing, because it can be *unsound*. Where
two passes answer the same question separately and each drives part of the emission, a
disagreement is not caught anywhere: each half is internally consistent, and what comes out
is a proof of something nobody asked for. R4.11c is the case that motivated the rule —
`[Frac]` and the write set both answered "does this method own its receiver", and the vtable
slot got a postcondition equivalent to `False` — and R9.6a is the same shape with a cheaper
symptom, one syntax node lowered against two different scopes. So: whenever a fact is needed
in two places, it is *computed* in one and *read* in the other.

The audit that followed R4.11c checked the rest of the pairs. `Declarations.IsReadOnly`
(call sites) and `IrMethod.IsReadOnly` (declarations) can differ in exactly one direction —
a concrete `[Frac]` method whose body writes — and that program is refused by Pulse anyway
(`test/pulse_refusals/cases/FracMutates.cs`). A non-mutating `override` filling a mutating
slot does translate, and verifies: the wrapper is checked against the slot's type by F\*,
which is the whole point. Where the two analyses differ, the verifier is what settles it.

**Rule 4 — No example is nameable from inside the compiler.** `Pal.Compiler` contains no
identifier drawn from the test suite. Enforced by `test/no-example-names.sh`.

Two mechanical detectors back these up — **variant tests** and the **provenance lint** —
stated in §7.2.

---

## 1. Validated Pulse facts

The rules below depend on the following, each **verified against the pinned toolchain**
(`tools/fstar`) rather than assumed. The facts were first established on nightly-2026-07-30
and re-checked on each upgrade since; the current pin is F\* built from source
(`tools/fstar-source.txt`): FStarLang/FStar#4798, which adds native Pulse exceptions, merged
with the master of nightly-2026-10-31, with Z3 5.3.0. That build's installed
`pulse/lib/fstar.include` omits the PR's `effects` directory (`Pulse.Lib.Effects.*`), and
`tools/install-fstar.sh` adds it back.

| # | Fact | Evidence |
|---|---|---|
| F1 | A `while` condition may be a **stateful statement block**, so short-circuiting guards that read memory need no flag-rotation encoding. | `pulse/lib/Pulse.Lib.Array.fst:41-42` uses `while (let vi = !i; if (vi < l) { a1.(vi) = a2.(vi) } else { false })`; reproduced locally in `W3.fst`, verified. |
| F2 | Every `while` in a terminating `fn` **requires `decreases`**; without it the loop is `stt_div` and fails to compose with the `stt` continuation ("Cannot compose computations in this divergent block"). | Reproduced locally: `W2.fst` fails, `W3.fst` succeeds with `decreases` added. |
| F3 | A `decreases` measure **may dereference mutable locals** (`!i`), but **may not** mention invariant-bound existentials. | `Pulse.Lib.Array.fst:49`, `Pulse.Lib.ArrayPtr.fst:385`; local `W3.fst` failed with `reveal v`, succeeded with `!i`. |
| F4 | Pulse source requires the `#lang-pulse` pragma after the module header and `open`s. | `pal/pulse/Pulse.Lib.C.Array.fst:9`; local `Smoke.fst`, verified. |
| F5 | The F* binary release bundles Pulse; no separate install is needed. | `tools/fstar/lib/fstar/pulse/` present after `make tools`. |
| F6 | Every support-library operation whose result is consumed inside a `while` guard **must** specify its result with `rewrites_to`, not `pure (x == …)`. A `pure` postcondition leaves the let-bound intermediate existentially quantified, and Pulse then cannot infer the guard's postcondition — it reports `Cannot find witness for exists* (t: …)`. | Discovered by the original insertion-sort study, now covered by the compiler tests in `test/insertion_sort`: both `Array.length_i32` and `Array.read` failed this way and were respecified with `rewrites_to`. Pulse's own `op_Dot_Lparen_Rparen` and PAL's `array_read_all` do the same. |
| F7 | `Pulse.Lib.Array` provides no SMT-patterned link between `Array.Core.length a` and `Seq.length s`; `pts_to_len` must be invoked explicitly. Modelling `a.Length` as a *pure* function of the array (sound, because a CLR array's length is immutable) avoids needing it at every guard. | `Pulse.Lib.Array.fst:38,65,117` all call `pts_to_len` by hand; `Pulse.Lib.CSharp.Array.arr_length` takes the pure route. |
| F8 | A **stateful block may appear in term position**, as the scrutinee of a `let`: `let t = if (c) { <stateful block> } else { e };` is well-formed Pulse. This is what makes the short-circuit rule R6.3 compositional — the same lowering serves a loop guard, an `if` condition and an assignment right-hand side, with no context-dependent special case. | `test/pulse_facts/PulseFacts.fst:short_circuit_in_term_position`, verified; relied on by every generated short-circuit. |
| F9 | A `decreases` measure may dereference a mutable local, but **not underneath an `if`**. `decreases (if !b then 0 else I32.v !r)` is rejected with "Expected type `FStar.Int32.t` but `!r` has type `fn …`", because the `!` sugar is elaborated only outside the branches. A conditional measure must keep its dereferences out of the branches. | `test/pulse_facts/PulseFacts.fst:decreases_conditional_without_deref`, verified; the failing form was reproduced while writing `test/binary_search`. |
| F10 | F\* resolves **module-qualified record syntax** in all three positions — projection `e.M.f`, update `{ e with M.f = v }`, and literal `{ M.f = a; g = b }` — without the defining module being `open`ed. So a generated struct module needs no `open` anywhere, and two structs may share a field name with no ambiguity. | `test/pulse_facts/PulseFacts.fst` + `test/pulse_facts/StructFacts.fst`, verified. |
| F11 | A record **update's source must be a pure term**: `{ !r with M.f = v }` is rejected ("Ill-typed term … got expression of type `fn … returns …`"), because `!r` is a stateful operation and the update is a term former, not a statement. The deref must be let-bound first. This does not contradict F8: F8 is about a stateful block as the *scrutinee of a `let`*, which is precisely the form that fixes this. | `test/pulse_facts/StructFacts.fst:struct_field_write`, verified; the failing form was reproduced while writing R3.4. |
| F12 | A Pulse `fn` **must have at least one binder**. A parameterless one fails in the elaborator, not the solver: "Tactic failed — main: FnDefn does not have binders". So a C# method with no parameters takes `()`. | `test/pulse_facts/StructFacts.fst:no_parameters`, verified; the failing form was reproduced by `test/point_struct`'s `Origin()`. |
| F13 | `preserves p` is a genuine `fn` spec clause, meaning exactly `requires p ensures p`, and it composes with `requires` and `ensures` on the same `fn`. | `test/pulse_facts/ObjectFacts.fst:count`, verified. Relied on by R4.11. |
| F14 | `Pulse.Lib.Box` is the **sound** heap cell and the right model of a CLR object. `Pulse.Lib.Reference.alloc` is marked `[@@deprecated "…is unsound; only use for model implementations"]` and may not appear in generated code; `Box.alloc` carries no such marker. `Box` additionally supplies `null`, a *pure* `is_null`, and `pts_to_not_null`, so a nullable object reference needs no new machinery. | `tools/fstar/lib/fstar/pulse/pulse/lib/Pulse.Lib.Reference.fsti:87` and `Pulse.Lib.Box.fsti:31-53,90-110`; `test/pulse_facts/ObjectFacts.fst:ownership_implies_non_null`, verified. Relied on by R3.8 and R3.11. |
| F15 | Pulse slprops are **affine**: `Box.free` exists but nothing compels a caller to reach it, and a leftover resource is discharged by `drop_`. So modelling a garbage-collected heap needs **no axiom at all** — allocate, never free. | `test/pulse_facts/ObjectFacts.fst:alloc_without_free`, verified: it allocates an array and a box, returns, and frees neither. Relied on by R3.12. |
| F16 | An object resource is linear, so passing the same object to two owned parameters is **unprovable**, reported as a bare `Error 228: Cannot prove: class_C__inv a _`. Aliasing is thus safe but incomprehensible, which is why R3.13 requires the emitter to diagnose it first. | `test/pulse_facts/ObjectFacts.fst:aliasing_is_unprovable` documents the rejected call; the failure was reproduced against the pinned toolchain. |
| F17 | A fact about the **model alone** is visible to a caller only if it lives in the model type as a *refinement*. Placed instead inside the object invariant it is unreachable: a caller holding `class_C__inv this m` cannot derive it without unfolding, and F* reports `Error 19` at the postcondition. | `test/pulse_facts/ObjectFacts.fst:client_sees_model_invariant`, verified; weakening `model_StackModel__pred` to `True` reproduces the `Error 19`. Relied on by R3.9d. |
| F18 | F15's affinity is a **permission to discard, not an automatic discard**. A method that allocates an object and does not return it still holds the invariant when it ends: `Error 228: Leftover resources: class_C__inv x _`. Writing the discard needs a name for the model the context holds — an existential witness the emitter never chose — which `with m. assert p;` binds. | `test/pulse_facts/ObjectFacts.fst:allocate_and_discard`, verified; the failure was reproduced by `test/counter_client`'s `FreshIsZero` before R4.14 existed. Relied on by R4.14. |
| F19 | F18's idiom works only where the postcondition is **known**. Inside a block in statement position Pulse is still solving for that block's post, and unifying the object's model existential against a uvar fails: `Error 339: Cannot find witness for …; Cannot check relation with uvars`. Binding the witness at the allocation, discarding `exists* m. inv x m` directly, and annotating the branch `ensures emp` all fail (the last one succeeds only for a branch that touches nothing else). | `test/pulse_facts/ObjectFacts.fst:allocate_in_a_returning_branch`, verified; the failing shape is `test/diagnostics/cases/ObjectInNestedBlock.cs`. Relied on by R4.14a. |
| F20 | An object's invariant may **contain** another's, and nesting needs no new device: the outer invariant existentially quantifies the sub-object's *model* exactly as R3.10a quantifies an array's *contents*. Inside the outer `unfold` window the sub-object stays **folded**, so calling its methods is an ordinary call. The closing `fold` must re-name the sub-models where it happens, because a call may have moved one. A bound on a sub-model reaches a call site only as a **refinement on the model type** — F17 again, and not optional: as a `pure` conjunct inside the sub-invariant it is behind a folded slprop and does not reach. | `test/pulse_facts/ObjectFacts.fst:ranked_mk`, `ranked_bump_left`, verified. Relied on by R3.10b. |
| F21 | An slprop `let` may take a **meta-argument-defaulted** permission binder, as `Box.pts_to` does: `let inv (this: C) (#[T.exact (`1.0R)] p: perm) (m: M) : slprop`. `inv x m` then *means* `inv x #1.0R m`. So indexing every class invariant by a permission changes no existing emission — full ownership stays what you get by not asking. | `test/pulse_facts/ObjectFacts.fst:frac__inv`, `frac_default_is_full`, verified. Relied on by R3.10c. |
| F22 | A per-class `share` is provable from `Box.share`, `Array.share` and each sub-object's own `share`. Each closing `fold` **must** be preceded by an `assert` naming the resources it consumes: the invariant's existentials are solved by matching against the context, and after a share the context holds two candidates for every one of them. | `test/pulse_facts/ObjectFacts.fst:frac__inv_share`, `frac_outer__inv_share`, verified. Relied on by R3.10d. |
| F23 | A per-class `gather` proves the two models **equal**. Not an extra hypothesis and not a choice: R3.9's invariant pins `m` to the abstraction function of the representation, `Box.gather` proves the two representations equal, and a function of equal arguments is equal. Two read-only aliases of one object therefore necessarily agree about it. It composes only if the two permissions are **explicit** parameters and the second view is renamed onto the first with `pts_to_injective_eq` *before* either is gathered — both matching problems, invisible at one level of nesting. | `test/pulse_facts/ObjectFacts.fst:frac__inv_gather_gen` and `frac_outer__inv_gather_gen` (a class owning a class, the smallest configuration that catches it), verified. Relied on by R3.10d. |
| F24 | Pulse normalises `p /. 2.0R +. p /. 2.0R` to `p` for `pts_to`, which has prover support, but **not** for a user-defined slprop, which is matched syntactically. | `test/pulse_facts/ObjectFacts.fst:frac__inv_gather` needs the arithmetic discharged by an explicit `rewrite`; `PermProbe`-style `Box.share; Box.gather` round-trips without one. Relied on by R3.10d, which states `gather` as `share`'s exact inverse so the arithmetic is discharged once. |
| F25 | Pulse does **not** split a permission at a call site. `f s s`, where `f` takes two independently-fractional parameters, fails with `Cannot prove: …__inv s _` against a context holding exactly that resource — for an object *and* for an array. Splitting is a proof step, and Pulse does not guess it. | `test/pulse_facts/ObjectFacts.fst:frac_alias`, `frac_alias_array`, verified with the `share` and failing without it. Relied on by R5.13. |
| F26 | Generalising a **read-only** method over the permission is a *pure* generalisation: a caller holding full ownership calls it unchanged, because Pulse instantiates the binder at `1.0R`. It is also **necessary for composition** — R3.10c propagates the outer fraction into a sub-object's invariant, so an owner's reader can only call its parts' readers if those are generalised too. | `test/pulse_facts/ObjectFacts.fst:frac_peek`, `frac_full_owner_reads`, `frac_outer_peek`, verified. Relied on by R4.11b. |
| F27 | **Two** views of one object may be in scope at once; **three** may not. Matching an slprop against the context is a search for a *unique* candidate, so after a second `share` there are three resources with the same head and the same name and the next call is refused. Two is what read-only aliasing needs, and more is reached by nesting share/use/gather. The permission itself splits without bound — it is simultaneity that is limited. | `test/pulse_facts/ObjectFacts.fst:frac_two_views` (verified), `frac_three_views` (`expect_failure`), `frac_split_thrice` (verified). Relied on by R3.10e. |
| F28 | **A vtable cannot be a `Box` payload.** `slprop : Type u#4`, so a record with an invariant field lives far above `Type0` — and `Box` needs a `Type0`. So an object reference cannot simply be a box of its vtable, which is what forces F29's `dyn`. (F28b: the restriction is `Box`'s, not Pulse's — a *plain* record is unaffected.) | `test/pulse_facts/InheritanceFacts.fst:49-82`, verified. Relied on by R9.8. |
| F29 | **`FStar.Dyn.dyn : Type0`, and `mkdyn` is universe-polymorphic.** Lowering a vtable-carrying object into `dyn` puts it back in `Type0`, so a reference into a hierarchy is boxable, arrayable and legal as a field. `mkdyn` is *not* injective (it cannot be, on pain of Cantor), which is the source of every remaining difficulty. | `test/pulse_facts/InheritanceFacts.fst:84-96`, verified. Relied on by R9.8, R9.11. |
| F30 | **`FStar.Dyn.undyn` cannot be called from Pulse.** It is in `Dv`, and `Dv` results cannot be equated in specifications, so recovering the object needs an axiom (`recover`) rather than a definition. It must be stated in `stt`, not `stt_div`: `stt_div a emp post` is inhabited for *every* `post` (F30b, verified by a hang), so an `stt_div` axiom would be free and worthless. (F30c: `stt` itself is a `Type0`.) | `test/pulse_facts/InheritanceFacts.fst:113-201`, verified. Relied on by R9.9, §8.4's one assumption. |
| F31 | **A stored Pulse computation must be let-bound before it is applied.** `ob.pkg.area x` does not run; `let f = ob.pkg.area in f x` does. Pulse runs an `stt`-valued term only as the head of an application. | `test/pulse_facts/InheritanceFacts.fst:203-256`. Held up to nightly-2026-08-05; since nightly-2026-10-31 Pulse also runs `ob.pkg.area x` directly, and both forms verify. The emitter keeps the let-binding, which is valid on both. Relied on by R9.12. |
| F32 | **The model may not be fixed per hierarchy.** A vtable fixes one model type, but a subclass needs its own; the base invariant existentially quantifies the subclass model and relates it by a pure forgetting function. This is R3.9's abstraction function one level up. | `test/pulse_facts/InheritanceFacts.fst:257-316`, verified. Relied on by R9.5, R9.6. |
| F33 | **A pack site must eta-expand every vtable slot.** F21 gives every class invariant a meta-argument-defaulted permission binder, which does not match a vtable field type until the slot is eta-expanded. | `test/pulse_facts/InheritanceFacts.fst:317-340`, verified. Relied on by R9.13. |
| F34 | **An upcast moves no memory.** `Shape s = c;` is a pure re-reading of the same reference, so it is a `ghost fn` and free at runtime — which is what C# requires of a reference conversion. | `test/pulse_facts/InheritanceFacts.fst:341+`, verified. Relied on by R9.14. |
| F35 | A `type … and …` group may **mix a record definition with a type abbreviation**, so a recursive class's representation, its reference type and its nullable form come out as one mutually recursive group and nothing new is needed to tie the knot. | `tools/fstar/lib/fstar/pulse/pulse/lib/Pulse.Lib.LinkedList.fst:14-16`; `test/pulse_facts/RecursiveFacts.fst:class_Node__raw`, verified. Relied on by R10.1. |
| F36 | An inductive ownership predicate must recurse on the **model**, not on the reference. By cases on the reference there is no measure F\* can see, because the sub-model is related to the model by a `pure` equation rather than by a pattern; by cases on the model the sub-model *is* a sub-term and `decreases m` is discharged with nothing written by the user. | `test/pulse_facts/RecursiveFacts.fst:class_Node__inv_opt`, verified. This is the fact that fixes §10's whole shape, and the reason R10.5 asks for the model as a function of the fields. |
| F37 | The five case lemmas of R10.4 are provable from the definition alone, and are placed by the **null test the C# already writes**. R4.10 opens a window around a field access; R10.6 opens the same window around the `else` branch of a null test. | `test/pulse_facts/RecursiveFacts.fst:class_Node__nil_case`, `elim_nil`, `intro_nil`, `elim_cons`, `intro_cons`, `cases`, all verified. Relied on by R10.4 and R10.6. |
| F38 | `decreases` on an **erased** model binder is accepted for a `fn rec`, and the recursive call's obligation is discharged by SMT from the `pure (m == hd :: tl)` that `elim_cons` hands back. So a recursive method needs no measure beyond naming its model. | `test/pulse_facts/RecursiveFacts.fst:func_Lists_Length`, `func_Trees_Size`, verified. Relied on by R10.6. |
| F39 | The ordinary field-write idiom (R3.12's `B.op_Colon_Equals var ({ t with … })`) composes with R10.4 unchanged: the window opened by a null test is exactly the window a field write needs. This is what makes a **destructive** traversal — `Append`, an in-place BST insert — verifiable. | `test/pulse_facts/RecursiveFacts.fst:func_Lists_Append`, `func_Trees_Insert`, verified. Relied on by R10.6b. |
| F40 | R3.10d's `share`/`gather` survive the induction: a `ghost fn rec` recursing on the model proves both, using the class's own case lemmas rather than `unfold`. | `test/pulse_facts/RecursiveFacts.fst:class_Node__inv_opt_share`, `class_Node__inv_opt_gather`, verified. Relied on by R10.7. |
| F41 | R3.10b — "a field of class type contributes that class's invariant at an existentially bound model" — applies **verbatim** when the field's type is nullable and recursive; only the predicate's name changes. So an ordinary M2 handle class over a recursive one needs no new rule. | `test/pulse_facts/RecursiveFacts.fst:class_LinkedList__inv`, `func_LinkedList_Push`, `func_LinkedList_Count`, verified. Relied on by R10.8. |
| F42 | Two recursive occurrences are no harder than one: the two sub-invariants sit side by side under `**`, which is what makes the two subtrees separately owned and hence what makes an in-place tree insert verifiable. | `test/pulse_facts/RecursiveFacts.fst:class_TreeNode__inv_opt`, `func_Trees_Insert`, verified. Relied on by R10.3. |
| F43 | A **back pointer** is expressible with no new device: the predecessor becomes an extra *index* of the predicate, the back pointer is constrained (`pure (r.fld_prev == left)`) rather than owned, and the recursive call passes the current reference as the new index. Reading the index *off the field* in `intro_cons` is what makes a write to `prev` a legal proof step. | `test/pulse_facts/RecursiveFacts.fst:class_DNode__inv_opt`, `func_DLists_Length`, `func_DLists_PushFront`, verified. Relied on by R10.10. |
| F44 | `[]` and `::` are *notation* for the ordinary prefix constructors `Nil` and `Cons`, which work in every position the notation does — as a term, as a **pattern**, and under the discriminator `Cons?`. So a scheme phrased over "the empty constructor" and "the non-empty constructor" covers `list` with no special case, and the emitter needs only a constructor *name* and an arity. | `test/pulse_facts/UserSpecFacts.fst:nil_is_prefix`, `cons_is_prefix`, `length_prefix`, `cons_test`, verified. Relied on by R11.5. |
| F45 | §10's whole encoding — the inductive invariant, all eight lemmas, the window, a recursive traversal and a destructive one — works verbatim over an inductive the **compiler has never heard of**, at a constructor arity that is neither a list's nor a tree's (two pure arguments and one recursive). Nothing in the template depends on which model type it is instantiated at. | `test/pulse_facts/UserSpecFacts.fst:class_Pair__inv_opt`, `class_Pair__elim_cons`, `func_Pairs_Count`, `func_Pairs_Set`, verified. Relied on by R11.6. |
| F46 | `FStar.Int.Cast` supplies a total function for every machine-integer width pair pal-csharp maps, and each is *modular*, not partial: it carries no precondition and truncates. So an explicit C# cast has a translation with no side condition attached — which matters, because C#'s default `unchecked` context defines the same truncation. | `test/pulse_facts/ConversionFacts.fst:cast_is_total`, `cast_truncates`, verified. Relied on by R13.1. |
| F47 | A cast is the identity on the mathematical value exactly when **every value of the source type is a value of the target** — which is strictly narrower than "the target is wider". `uint8 -> int8` and `int32 -> uint32` are both same-width and both lossy. | `test/pulse_facts/ConversionFacts.fst:widening_is_identity`, `same_width_is_not`, verified. Relied on by R13.2. |
| F48 | A *narrowing* cast's mathematical value is `% pow2 n` when the target is unsigned and `FStar.Int.op_At_Percent` when it is signed; the two do not coincide. | `test/pulse_facts/ConversionFacts.fst:narrowing_unsigned`, `narrowing_signed`, verified. Relied on by R13.2. |
| F49 | When the source value is already in the target's range, the modular reading collapses back to the exact one, so a user who proves the range gets exactness with no extra rule. | `test/pulse_facts/ConversionFacts.fst:narrowing_in_range`, verified. |
| F50 | `FStar.Int` has **no** `logand_mask`. The route to a masking fact is `Int.logand a b == Int.from_uint (UInt.logand (Int.to_uint a) (Int.to_uint b))`, which holds by `()` because `to_vec`, `from_vec` and `logand` are plain reducible `let`s, followed by `FStar.UInt.logand_mask`. | `pulse/Pulse.Lib.CSharp.Casts.fst:int_logand_as_uint`, verified. Relied on by `byte_mask_ff`. |
| F51 | `FStar.UIntN.shift_left` takes its shift amount as a **`UInt32.t` whatever the operand's width is**, so a shift whose amount C# writes as an `int` needs a conversion on the amount and only on the amount. | `test/pulse_facts/ConversionFacts.fst:shift_amount_width`, verified. Relied on by R13.5. |
| F52 | `FStar.UInt.logor_disjoint` needs a **positive** shift amount; at zero the lemma does not apply even though the equation still holds. A general packing lemma must exclude `0`. | `pulse/Pulse.Lib.CSharp.Casts.fst:logor_shift_disjoint`; the `m: pos` requirement was reported by the checker. |
| F53 | An SMT pattern may be placed on the **idiom** rather than on a named lemma — `[SMTPat (int32_to_uint32 (logand (uint8_to_int32 b) 255l))]` fires on the shape `(uint)(b & 0xff)` compiles to. This is how a language-level idiom is made free of annotation without the emitter knowing anything about it. | `pulse/Pulse.Lib.CSharp.Casts.fsti:byte_mask_ff_bound`, `logor_shift_disjoint`; relied on by `examples/adler32`, which needs no annotation for either idiom. |
| F54 | SharpZipLib's Adler-32 comment is **arithmetically wrong in the unsafe direction**: the true supremum of `s2` before the deferred modulo is 2 090 626 020, not the 2 090 079 800 the comment claims — larger by 546 220, because "median(s1)" approximates a triangular sum. The conclusion (`< 2^31`) survives, with 2.65% headroom rather than 2.68%. The claim about `s1` (max 1 034 520) is right. | `test/pulse_facts/ConversionFacts.fst:tri`, `tri_closed`, `adler_s2_bound`, `adler_comment_understates`, verified. |
| F55 | A `[Spec]` function's parameters are all mathematical (R4.6) whatever their C# types, but a `[Lemma]`'s binders keep the types they were declared with (R4.7). Argument coercion is therefore **not** a property of the argument alone. | The two emitted signatures differ: `Let_RingVariant_Slot` takes `(var_head: int)` from a C# `int`, `Let_Adler32_Step` takes `(var_off: I32.t)` from the same C# type. Relied on by R13.6. |
| F56 | A slot is a *binding*, and a binding introduced inside a block is out of scope once the block closes — including for R5.13's resource-naming bracket, which would otherwise assert `pts_to` for a cell whose Pulse binder no longer exists ("Identifier not found: var_n"). | Reproduced by a `Pal.Assert` placed after a loop whose body declared a local; fixed in `CodeEmitter.Scoped`. |
| F57 | A pass that analyses a body and a pass that rewrites it are **ordered**, and the analysis must see the rewritten form. R5.7 asks whether a loop body escapes, in order to decide whether the `for` step goes in the body or in its own slot; asked of the body *before* R5.14 has run, the question is answered "no" for a `continue` still sitting inside a `switch`, the step is appended to the body, and the step is then skipped on the very iterations that continue — so the measure stalls and termination fails. | Reproduced by `test/switch_stmt:Count`, whose `case 7: continue;` failed with `pow2 31 - (match … with \| true -> i+1 \| false -> i) << meas`. Fixed by asking `Escapes` of the normalized body. |
| F58 | A desugaring that introduces a binding must **splice** into its enclosing block, not nest inside a fresh one. R5.14's scrutinee binding wrapped the if/else chain in a block, and R5.5b absorbs a tail only into a chain that is a statement of the same block — so `switch (t) { case k: return e; } return d;` was rejected even though every piece of the rule was right. | Reproduced by `test/switch_stmt/SwitchVariant.cs:WeightOf` (three `PALCS0001`s). Fixed by carrying the binding in `IrSwitch` and splicing the expansion in `Normalize`. |
| F59 | Pulse's `match` **can** scrutinise a machine integer, since FStarLang/FStar#4374 (merged 2026-08-02); before it, `0l` in pattern position was read as a `Prims.int` and rejected against an `Int32.t` scrutinee. But an arm's hypothesis is just the equality `I32.v k == 0` — a machine integer is not an inductive type, so there is no case split to be had that an `if` does not already give. | `test/pulse_facts/MatchFacts.fst:match_i32`, `match_u8`, and `match_gives_equality` beside `chain_gives_equality`, which discharge the same assertion. Requires the toolchain pinned at 2026-08-05 or later. |
| F60 | **Pulse has no or-patterns**, though F\* does. `match k { 0l \| 1l -> … }` is a syntax error, while `let f n = match n with \| 0 \| 1 -> 10 \| _ -> 1` verifies. A C# section carries a *set* of labels, so `match` can express `case 0: case 1: S; break;` only by duplicating `S` once per label, without bound. | `test/pulse_facts/MatchFacts.fst` §4 records the error (`Error 168: Syntax error`) and the disjunction that replaces it. This is what decides R5.14 against `match`. |
| F61 | **C's implicit fallthrough is what forces PAL's `hit` flag.** `pal/cpp/impl.cpp` desugars `switch` into a *sequence* of `if (!brk && (hit \|\| scrut == v))` guards with two threaded flags; C# forbids fallthrough (CS0163), so its sections are disjoint and a plain if/else chain suffices with neither flag. | Read from `pal/cpp/impl.cpp:1834`. This is why R5.14 does not import PAL's machinery, and why `goto case`/`goto default` — the one way back into fallthrough — are refused rather than approximated. |
| F62 | **`Pulse.Lib.CSharp.Array` already works at an abstract element type.** `CA.read`/`CA.write` are declared `(#t: Type0)`, so a Pulse `fn` polymorphic in `t` can call them with the type variable it was given. A generic method over `T[]` therefore needs no new library. | `test/pulse_facts/GenericFacts.fst:generic_get`, `generic_set`. This is the fact that makes generics a frontend milestone rather than a library one. |
| F63 | **A generic struct is an ordinary parameterised record.** `noeq type segment (t: Type0) = { arr: A.array t; off: I32.t; cnt: I32.t }` and a pure predicate over it both typecheck, and a Pulse `fn` over the record verifies. This is the `ArraySegment<T>` / `Span<T>` shape. | `test/pulse_facts/GenericFacts.fst:segment`, `seg_ok`, `seg_first`. `examples/adler32` had to spell `ArraySegment<byte>` out as three parameters; this is why it will not have to. |
| F64 | **Instantiation composes.** A generic `fn` may call a generic `fn` at its own type variable, with the type argument inferred exactly as a concrete one is today. So generic methods calling generic methods need no monomorphising pass. | `test/pulse_facts/GenericFacts.fst:generic_swap`, which calls `generic_get`/`generic_set` at `t`. Without it the emitter would have to specialise every instantiation, losing the module-per-method structure §2 depends on. |
| F65 | **A C# `string` needs no separation logic.** It is immutable, so there is nothing to own: it is a pure value, `Seq.seq char` is an adequate model, and a Pulse `fn` takes and returns one under `requires emp`. | `test/pulse_facts/StringFacts.fst`. Recorded as the road not taken in M8: the *encoding* is cheap, and the cost of strings is the library surface (`Substring`, `IndexOf`, `Split`, concatenation), not the model. |
| F66 | **A mutually recursive type group may be parameterised.** R10.1's record, its `box` abbreviation and its `option` abbreviation each repeat the binder, and the recursion is at the *same* type argument — which is all a C# `Node<T>` can say, since `Node<T>.next` is a `Node<T>?` and never a `Node<U>?`. | `test/pulse_facts/GenericClassFacts.fst:class_Node__raw`. |
| F67 | **A model type carries its refinement across parameterisation.** R3.9d's `[Refine]` predicate is a predicate *on the model*, so it is parameterised exactly as the model is: `class_Node__model (a: Type0) = m: list a { pred m }`. | `test/pulse_facts/GenericClassFacts.fst:class_Node__model`. |
| F68 | **A class's type parameter is *implicit* on every generated definition, and that is not a hope about inference.** Each of the twelve definitions R10.4/R10.8 emit has a value argument whose type already mentions the parameter (`x: class_Node__opt a`), so it is determined by unification with an argument the emitter writes down anyway. The payoff is that every *call site* §10 emits stays character for character what it already is. | `test/pulse_facts/GenericClassFacts.fst` F68–F70: `class_Node__inv_opt`, the six case lemmas and the recursive share/gather all take `(#a: Type0)`, and `func_Lists_Length` calls them with no type argument at all. |
| F69 | **A generic method over a generic class composes the two rules and needs no third.** An explicit `ty_T` binder (R14.2) applied to a class type (`class_Node__opt ty_T`), with the class's own lemmas inferring `a` from it. | `test/pulse_facts/GenericClassFacts.fst:func_Lists_Length`. |
| F70 | **A probe written outside the emitter's idiom measures the probe.** The first draft of F69 failed with "Application of a stateful or atomic computation cannot have a ghost effect"; a control at a *fixed* element type failed identically, and both succeeded once rewritten in R10.7's actual shape — an `erased` model with `requires`/`ensures` spelled out rather than `preserves`. Generics were never involved. | `test/pulse_facts/GenericClassFacts.fst:ctrl_Length`, kept beside `func_Lists_Length` as the control. |
| F71 | **The part of a structure a loop has walked is a function of the loop counter.** So it can be named by a total function (`Take`/`Drop`; `Ctx`/`Sub`) rather than accumulated in a ghost variable, and closing it at the end is an ordinary lemma about the user's segment predicate — not the magic wand §10.7 refused for. | `test/pulse_facts/CursorFacts.fst`, `test/pulse_facts/TreeCursorFacts.fst:knot_find`, verified. Relied on by §16. |
| F72 | **A branching cursor needs no more loop machinery than a linear one.** A *search* path is determined by the tree and the key, both fixed for the loop, so a one-hole context is as much a function of the counter as a prefix is. The context lemmas recurse on the **tree** (`decreases t`), which keeps the counter an unrefined `int`. | `test/pulse_facts/TreeCursorFacts.fst:dsub`, `dctx`, `path_append`, `path_close`. |
| F73 | **An `exists*` binder that appears only inside `pure` can never be solved.** Pulse's matcher recovers a binder from the `pts_to`s it unifies; folding a predicate whose existential has no resource to be recovered from fails with "Cannot check relation with uvars". This is what decides whether a predicate may hide a machine value (R16.3). | Reproduced while writing `TreeCursorFacts.knot_open`; resolved by the explicit-field-plus-wrapper shape now in `KnotPath.fst`. |
| F74 | **Pulse cannot disambiguate two conjuncts of one predicate whose only difference is a pointer just read from the heap.** The fix is definitional, not a lemma: make each conjunct's model half a total projection (`subl`/`subr`) of a model the invariant already names (R16.2). | Reproduced in `TreeCursorFacts.knot_open`; the projections are in `KnotPath.fst`. |
| F75 | **A Pulse `let mut` needs a postcondition at the end of its scope.** A field read inside the non-null branch of a test binds a cell, so the same branch is typable as a method's tail and untypable one statement short of it — which is why a loop body's last statement must be emitted in tail position (R5.8d). | Diagnosed by hand-editing `test/tree_cursor/out/Func_Search_Find.fst`: removing the *outer* trailing `()` was the change that mattered. |
| F76 | **A Pulse `box` is already a nullable pointer.** `Pulse.Lib.Box` exports `null`, `is_null (r: box a) : b:bool{b <==> r == null}` and `pts_to_not_null`. So `option (box …)` is a *second* nullability layer over one that already exists, and its entire content is the two coercions R10.2b/R10.2c used to describe. Replacing it with a refinement (`class_C = b: class_C__opt { not (B.is_null b) }`) makes both coercions the identity text, deletes a `pure`-trapped existential from every recursive invariant (cf. F73), and lets each user-written cursor lemma take its cursor once instead of twice. | `test/pulse_facts/NullFacts.fst` N1–N7, verified; `tools/fstar/lib/fstar/pulse/pulse/lib/Pulse.Lib.Box.fsti:33,35,108`. Relied on by R10.2, R10.2b, R10.2c, R10.2d. |
| F77 | **Pulse does not see through an ordinary `let` when matching resources.** `class_C__inv this p m` and `class_C__inv_opt this p m` are the same term after delta, but a goal stated with one is not found in a context holding the other; an explicit `rewrite … as …` is required. This is why R10.2b being the identity *conversion* still leaves `class_C__as_opt` and `class_C__intro` in place as one-line rewrite lemmas rather than deleting them. | Reproduced in `test/pulse_facts/NullFacts.fst` while writing `inv_share`/`inv_gather_gen`. |
| F78 | **`Pulse.Lib.Slice` is the `Span<T>` shape, and the whole of what is missing is on the C# side.** A `slice t` is a first-class value with a non-ghost `len`, a `pts_to` over its contents, `split`/`join`, `subslice` with a `subslice_rest` residue, `share`/`gather`, `copy`, and an `is_from_array` provenance token. Returning a subslice is *derivable* from the two `is_split`s `subslice_rest` is defined over — no library request is needed. What is not derivable is knowing *where in a C# program* the split and the join happen. | `test/pulse_facts/SliceFacts.fst` S1–S6, verified; `tools/fstar/lib/fstar/pulse/pulse/lib/Pulse.Lib.Slice.fsti`. Relied on by R17.1 and R17.5. |
| F79 | **A span value may be copied; the span's resource may not.** After `var t = s;` there is still exactly one `pts_to`, so a write through either name is a write to the memory both describe. This is precisely the duplication `PALCS0511` refuses a struct with a reference-typed field (§3.4) — and a `Span<T>` *is* such a struct. So a span cannot go through §3's struct rules; it has to be a **slot kind**, like `T[]`. | `test/pulse_facts/SliceFacts.fst:s4_copy_is_alias`. Note the `rewrite` the probe needs to move the resource between the two names: F77 again, and it is why the aliasing is invisible to Pulse's matcher unless the translation makes it explicit. |
| F80 | **`give_back w` recovers everything by unification.** A ghost operation whose only explicit argument is the window recovers the parent, the permission, the bounds and both contents from the receipt sitting in the context. This is what lets `Pal.Restore(w)` be a one-argument surface intrinsic (R17.6) rather than something that has to restate what was borrowed. | `test/pulse_facts/SliceFacts.fst:s8_restore_by_unification`, verified. Relied on by R17.6. |
| F81 | **A receipt may not be indexed by `SZ.t` if its bounds are `exists*`-bound.** `Pulse.Lib.Slice.subslice_rest` carries the refinement `SZ.v i <= SZ.v j /\ SZ.v j <= Seq.length v`, which cannot be discharged for bounds bound by an existential — the receipt fails to typecheck. Putting the refinement in a `pure` *inside* the `exists*` does not help: it is not available where `subslice_rest` is typed. The fix is to inline `subslice_rest` into a predicate indexed by `nat`, moving the refinement onto that predicate's own binder. | `pulse/Pulse.Lib.CSharp.Span.fst`'s internal `rest`; found while writing `is_range_of`. Relied on by R17.5. |
| F82 | **A `fold` does not normalise its indices.** `fold (rest s w p (I32.v i) …)` fails against a context holding `rest s w p (SZ.v lo) …` even where `SZ.v lo == I32.v i` is known to SMT; an explicit `rewrite … as …` first is required. F77 in a second guise, and the reason the library's borrow operations are written with a `rewrite` before each `fold`. | `pulse/Pulse.Lib.CSharp.Span.fst`, `intro_rest`. |
| F83 | **A pure lemma must be called before the resource step it supports, not after.** `splice_same v i j; restore_range w;` verifies; the reverse order does not — the resource match happens first and has already failed by the time the lemma runs. Erased arguments must be passed `(reveal v)` explicitly. | `test/pulse_facts/SliceFacts.fst:s9_read_only_trip`. |
| F84 | **A `prop`-valued definition's body reaches Z3 as native quantifiers (FStarLang/FStar#4519, since nightly-2026-10-31), so its `forall` needs a pattern.** Without one Z3 chooses its own trigger: a `[Spec]` `Sorted` over a sequence was instantiated ~20k times per query, and inside the loop that sorts the sequence even the decreases check `j - 1 + 1 << j + 1` timed out. Adding "the natural patterns" — the element reads — fixed it at the default rlimit, as it did F*'s own ulib. Hence R6.7b. | `test/insertion_sort_sorted`, verified at the default rlimit with R6.7b and not without it. |
| F85 | **A record literal in a Pulse statement or tail position must be parenthesised (since nightly-2026-10-31).** `{ M.f = …; … }` there is read as a block and fails with "Module name M … not in scope"; as a `let` right-hand side, or as `({ … })` anywhere, it is a record. The emitter parenthesises every record literal and functional update. | `test/pulse_facts/StructFacts.fst`, `test/point_struct`. |
| F86 | **A Pulse `try` is not framed, and its `ensures` defaults to `emp` (FStarLang/FStar#4798).** Whatever the context holds when the `try` starts and is not named in its `ensures` is lost after it, and whatever is not named in its `raises` is lost to the handler. So both clauses must own every resource live across the `try`, exactly as a loop invariant must (R5.8b). A `let mut` cell is reclaimed when an exception passes its scope, so a `raise` inside a block need not mention the block's own cells. | `test/pulse_facts/ExceptionFacts.fst`: P2 raises from a loop holding a cell, P3 owns a cell across a `try`, and P4, which names nothing, is `expect_failure`. |
| F87 | **A `fn` with no `raises` clause must prove it raises nothing.** The default is `raises (fun _ -> pure False)`, so a handler's closing `raise ex` for the classes it does not handle is a proof obligation, discharged by the `try`'s `raises` saying the exception is one of those it handles. `raise e` has every type, so it may be a statement, a branch's value or a tail. A handler is entered with what the `raises` says and nothing else: the facts a callee's `raises` stated about the exception are gone, apart from those the `try`'s `raises` restates. | `test/pulse_facts/ExceptionFacts.fst` P3; `test/throw_catch/Throwing.cs:Classify`, which declares no `[Throws]`. |
| F88 | **A raise with no expected type is `unit`.** In a branch of an `if` whose type comes only from a `let x : T =` annotation, `raise e` is typed `unit` with postcondition `pure False`; `raise e; let _ = elim_pure_explicit False; false_elim #(T) ()` is a `T`. | `test/record_cases/Shapes.cs:Next`, `ColorOf` (R21.7). |
| F89 | **The join of an `if` whose branches differ in shape can lose the facts of one.** `if c { stmts; t } else { false }` kept nothing from the then-branch; let-binding the bare `false` in its branch restores the join. | `test/record_cases`, and dmn-feel's `RangeEqual` (R21.4). |

F1 and F8 together **retire** the plan's original top risk: no `cont`-flag rotation and no
auto-generated short-circuit invariants are needed. F2 introduces a new obligation
(R5.9). F6 and F7 are constraints on the *library*, not on the emitter, and are the reason
`Pulse.Lib.CSharp.Array` is not a thin `include` of `Pulse.Lib.Array`.

Two further points of Pulse syntax, learned the hard way and pinned by the same test:
a `decreases` clause on a `while` takes **no trailing semicolon**, and a recursive F\*
definition needs `: Tot t (decreases m)` rather than `: t` followed by `(decreases m)`.

One semantic fact matters more than any of these for anybody *writing* annotations:
**a Pulse loop body sees the invariant and nothing else.** Pure facts from the enclosing
`requires` are not in scope inside the loop. Any precondition the body still needs must be
restated as an invariant. This is by far the most common annotation fix, and it is not
something the translator may paper over (§0, rule 3).

---

## 2. Modules, names, and output layout

Following PAL's conventions.

| C# declaration | Emitted module |
|---|---|
| method `C.M` | `Func_C_M.fsti` (signature + contract) and `Func_C_M.fst` (body) |
| `struct S` | `Struct_S.fst` |
| `abstract class C` | `Class_C.fsti` (what a subclass and a client may use) and `Class_C.fst` (the encoding — R9.17) |
| `sealed class C : P` | `Class_C.fst`, plus `Vtbl_C.fsti` / `Vtbl_C.fst` for its vtable and casts |
| `[Spec]` method `C.P` | `Let_C_P.fst` |
| `[Lemma]` method `C.L` | `Let_C_L.fst` |
| `[PulseType]` type `T` | `Type_T.fst` |
| `IncludePulse("M", …)` | `M.fst` |
| static field | `Global_F.fst` |
| — | `TranslationErrors.fst` — contains `let _ = assert False` iff translation reported errors, so running F* on the output directory always surfaces translation problems |

**R2.1 (naming).** A C# method `Ns.C.M` emits `fn func_C_M` in module `Func_C_M`. A
parameter `p` becomes the Pulse binder `var_p`. A local `x` becomes `var_x`. A `[Spec]`
function becomes `spec_C_P`, a `[Lemma]` becomes `lemma_C_L`. Name mangling is a pure
function of the source name; the emitter never chooses names by inspecting a program's
meaning.

PAL can name a module after the function alone, because C has a single global function
namespace. C# does not — two classes in one program may each declare `Abs` — so the
declaring type is always part of the name. Always, not only on collision: a program's
generated module names must not change when an unrelated class is added.

**R2.1a (overloads).** C# also lets *one* type declare `Abs` twice. Where the type
qualifier is added always, the signature is added **only to an overload set** — a member
whose `⟦name⟧` is shared by another member of the same type takes a suffix built from its
parameter types, `_`-joined, an empty list rendering `_unit`:

| C# | module |
|---|---|
| `class Over { int Id(int a); }` | `Func_Over_Id` |
| `class Over { int Id(int); int Id(int,int); }` | `Func_Over_Id_int`, `Func_Over_Id_int_int` |
| `class Box { Box(int); Box(); }` | `Func_Box__ctor_int`, `Func_Box__ctor_unit` |

The two halves of the rule are asymmetric on purpose, and the asymmetry follows from what
each protects against. The type qualifier guards against a collision an author cannot see —
`Abs` in another class, written by someone else — so it must not depend on whether that
other class exists. A signature suffix guards against a collision the author is looking
directly at, in one type, and the edit that introduces it is an edit to that very
declaration. Suffixing always would pay for that with `Func_Counter_Get_unit` throughout
every program that has no overload at all, and readable generated Pulse is the property
§2 exists to protect.

Constructors are why the rule is needed rather than merely nice. A method can be renamed
by its author; `.ctor` cannot, so without R2.1a a class may declare exactly one
constructor. That was the state before this rule, and it was not enforced — it *crashed*,
in `SpecBinder`, before any check ran. Which is R18.3 again: **the first pass that reduces
two declarations to one name must be the one that reports it.** Both places that key a
dictionary by this name now tolerate a duplicate and let `PALCS0501` report it, so a
sanitisation that happens to collide (`A.B` and `A_B` reach the same token) is a
diagnostic rather than a stack trace.

The set is computed over *definitions*. A call to `Exchange<int>` presents Roslyn a
constructed symbol which is not equal to the `Exchange<T>` in the type's members, so a
generic method compared naively is an overload of itself — and R15.1 says a generic method
emits one module for all its instantiations, so the suffix would name a module nothing
generates. The suffix is likewise built from the definition's parameter types, which is
what makes `Exchange<int>` and `Exchange<byte>` agree on it.

A parameter type becomes a token by taking its C# spelling and replacing everything that
is not an identifier character with `_`: `int` is `int`, `Span<int>` is `Span_int_`,
`int[]` is `int__`. The tokens are not meant to be pretty, only stable, injective in
practice, and derived from what the author wrote — R2.1's "a pure function of the source
name" applies to the suffix too.

**R2.2 (provenance).** Every emitted construct records the Roslyn `Location` it came from,
written to `source_range_info.json` as
`{module, file, construct, source: {file, range}}`. A module whose whole text is the
user's own Pulse (`[assembly: IncludePulse]`) records the single construct `"*"`.

`test/provenance-lint.sh` reads the generated `.fst` and `.fsti` files — not the compiler's
account of what it did — extracts every top-level `fn`, `let`, `let rec`, `val` and `type`,
and requires each to
appear in `source_range_info.json` with a span in a C# file that exists. A construct with
no provenance was invented by the translator, and anything the translator invents must be
justified as a numbered rule in this document rather than as a response to one example.
An emitter that *forgets* to record a construct therefore fails exactly as loudly as one
that invents it. The lint runs in `make -C test` and in CI, alongside
`test/no-example-names.sh`; together they are §7.2's two mechanical detectors.

**R2.3 (reading the verifier's answer back).** R2.2 answers "what does this construct come
from". The other direction — "what is this *line* about" — is what turns an F* error into
something a C# programmer can act on, and it is the reason the frontend does not need to
pre-empt the prover.

The emitter records, for each line of each generated module, the `IrLoc` it was emitting
for, written to `line_map.json` as `{file, fallback, lines: [{line, source}]}`. A statement,
a clause of a contract and a declaration each claim a line; the temporaries, folds and
discards between them claim none, and are read as belonging to the last construct that
started at or before them. `palcs report` consumes F*'s `--message_format json` on stdin,
maps each message through that, and writes `verification.txt` — a flat tab-separated file,
not JSON, because it is read inside a Roslyn analyzer where a dependency that fails to load
is a silently missing feature rather than an exception.

Three properties are deliberate:

* **The message is F*'s, verbatim.** Only the location changes. A tool that rewrote a
  prover's explanation into something friendlier would be paraphrasing a proof it did not
  perform, and the first time the paraphrase was wrong there would be no way to tell.
* **The reporter passes judgement on nothing.** It exits zero whatever it read; `pipefail`
  in `test/verify.mk` is what keeps a failed proof a failed build. A filter that could also
  fail the build would make a passing build depend on it having understood the output. For
  the same reason it never consumes what it did not recognise: F*'s prose ("Verified
  module: M") goes through untouched, and a message it could not place is printed at the
  location F* gave it. A filter standing in a build's only output stream may relocate, but
  it may not silence.
* **A warning that maps only to the module's fallback is dropped.** F* warns about its own
  caches and options against ranges in files nobody wrote; claiming those are about a
  particular class would be an invention. An *error* is reported wherever it lands, because
  an error the user cannot see is worse than one in roughly the right place.
* **`use` before `def`.** An F* range has two halves: `def`, the declaration the error was
  raised against, and `use`, the sub-term that provoked it. Either may point outside the
  translation — when a library definition is at fault, `def` is the library and `use` is
  the generated module — so each is tried and skipped if it does not map. When *both* map,
  `use` is the narrower and is the one reported: `def` for a Pulse `fn` can be the whole
  function. The order used to be the other way, and an array-bounds failure was announced
  against the enclosing method's signature rather than the index that caused it
  (`test/pulse_refusals/cases/IndexInBounds.cs`).
* **The implicit exit belongs to the method.** A body's trailing `()` is not the statement
  above it: it is the point at which the postcondition is proved, and it is located at the
  method. The alternative — inheriting the last statement's location, which is what the
  emitter used to do — is right only when the last statement happens to be the culprit, and
  charging a construct because it is *usually* to blame is the same invention §0 rule 3
  forbids elsewhere. `test/pulse_refusals/cases/BorrowNotReturned.cs` is the case that
  distinguishes them: it writes through a span, the write is fine, and it is the method
  that can no longer say anything about the array it lent out. An explicit `return` keeps
  its own location, because there the author did write the exit.

None of this is visible to a verification test. A proof that succeeds reports nothing, so a
wrong location can only be seen in a suite of programs that must fail: §8.2.

The line map is a separate file from `source_range_info.json` rather than a field in it:
they answer different questions, one is read by the provenance lint and the other by the
reporter, and a single file answering both is one neither reader can skim.

For how this reaches an editor, see §8: the analyzer reads `verification.txt` through
Roslyn's `AdditionalFiles`, which is change-tracked, so re-running `make` updates the
squiggles and nothing has to invalidate a cache by hand.

**R2.4 (the output directory is the translation, not a log of translations).** The set of
`.fst`/`.fsti` files in `-o` after a run is exactly the set R2.1 names for this program.
A module the previous run wrote and this one does not is deleted.

Write-if-changed, which R2.1's naming makes possible and which keeps F*'s checked-file
cache warm, has a failure mode if it is the *only* rule: rename `Shape.Area` to
`Shape.GetArea` and `Func_Shape_Area.fst` stays on disk forever, still listed by the
directory's `Makefile` glob, still verified, still failing — and it fails against a C#
declaration that no longer exists, so there is nothing to fix and no way to see why. The
same thing happens whenever a rule *stops* emitting a module, which is how this was found:
R9.20's collector briefly claimed R9.6's overrides, and the modules it wrote for them
outlived the fix and were caught by the provenance lint, which asks precisely "did any C#
ask for this?".

The other half of the rule is that **the same input emits the same bytes**. That is not
free: the emitter's slot table was an `ImmutableDictionary`, which enumerates in hash order,
and .NET randomizes string hashing per process — so the order the locals were named in a
`with va_5 vindex_6. assert (…)` line differed between runs of the same file, and
write-if-changed rewrote and F* re-verified a module that had not changed, at random, in
about one run in three. The fix is to enumerate in declaration order. The general form of
the rule is worth stating because the same trap is available anywhere in the emitter: **a
hash-ordered collection may be used for lookup and never for emission.**

Pruning is unconditional, including when translation had errors. `TranslationErrors.fst`
already makes an errored output fail, so there is no state worth preserving across a failed
run, and a rule that pruned only on success would leave exactly the case that motivates the
rule — a rename that also introduced an error — behaving as before. Only files matching
R2.1's extensions are removed; `_cache/`, `diagnostics.json` and the two maps are the
tool's own and are left alone.

**R2.4a (a verification result does not outlive the translation it describes).**
`verification.txt` is the other direction of R2.2: `palcs report` writes what Pulse said,
mapped back to the C# it was about, and the analyzer reads it so that a failed proof
appears on the source line responsible. It is deleted at the start of every translation.

Left in place it is the same failure as an unpruned module, one layer up. The symptom that
found it is worth keeping because it is so misleading: after R9.12b's bug was *fixed* and
the tree re-translated, `dotnet build` still reported

```
Quadrilateral.cs(33,23): error PALCS0600: Expected expression of type FStar.Int32.t
                                          got expression () of type Prims.unit
```

— a proof failure from a translator that no longer existed, on a line that no longer
produced it, reported by the C# compiler. Nothing was wrong; the *file* was wrong.

The deletion is unconditional rather than conditional on the translation having changed,
and the reason is the general one: **a conditional repairs the transition, a rule repairs
the state.** Deleting only when a module was written fixes the case that produced it and
leaves every file dropped by an interrupted run, a crash, or an older build in place
forever. It costs nothing because F* writes a `.checked` file only when a module
*verifies*: a module that failed has none, the harness therefore re-verifies exactly the
failing modules, and any real failure is restated on the next `make verify`. There is no
result that unconditional deletion can lose.

---

## 3. Types

**R3.1 (scalars).** `bool→bool`, `int→Int32.t`, `uint→UInt32.t`, `long→Int64.t`,
`ulong→UInt64.t`, `byte→UInt8.t`, `sbyte→Int8.t`, `short→Int16.t`, `ushort→UInt16.t`,
`char→UInt16.t`, `nint→PtrdiffT.t`, `nuint→SizeT.t`. `SpecInt→int`, `SpecNat→nat`,
`Seq<T>→Seq.seq ⟦T⟧`, `SlProp→slprop`. `float`/`double` are rejected (§8.5).

**R3.2 (ownership from the C# type system).** C# already encodes what PAL needs explicit
macros for. No attribute is required for any of these:

| C# parameter | Pulse binder | `requires` | `ensures` |
|---|---|---|---|
| `T x` (value) | `var_x: ⟦T⟧` | — | — |
| `ref T x` | `var_x: ref ⟦T⟧` | `pts_to var_x v` | `pts_to var_x v'` |
| `out T x` | `var_x: ref ⟦T⟧` | `pts_to_uninit var_x` | `pts_to var_x v'` |
| `in T x` | `var_x: ref ⟦T⟧` | `pts_to var_x #p v` | `pts_to var_x #p v` |
| `T[] a` | `var_a: A.array ⟦T⟧` | `A.pts_to var_a s` | `A.pts_to var_a s'` |
| `Span<T> a` | `var_a: Span.span ⟦T⟧` | `S.pts_to var_a s` | `S.pts_to var_a s'` |
| `ReadOnlySpan<T> a` | `var_a: Span.span ⟦T⟧` | `S.pts_to var_a #p s` | `S.pts_to var_a #p s` |

Attributes are needed only for the residue: `[Consumes]`, `[Plain]`, `[Frac]`, `[NonNull]`,
`[CoreRef]`.

**R3.3 (the index bridge).** C# array lengths and indices are signed `int`; Pulse arrays are
indexed by `SizeT`. This crossing is pervasive, so it is fixed here once and never decided
per-example:

* `a.Length` ⟶ `Pulse.Lib.CSharp.Array.length_i32 var_a : Int32.t`, whose result
  `rewrites_to` the **pure** model `arr_length var_a` (F6, F7). Purity is not an
  optimisation: a CLR array's length is fixed at allocation, so `a.Length` genuinely is a
  function of `a`, and modelling it that way is what makes a counted `for` over an array
  — where `a.Length` appears in the *guard* — translatable at all. `arr_length` returning
  `Int32.t` is also where the bound `length a < 2^31` enters. `A.array` is
  `Pulse.Lib.CSharp.Array.Base.array`: a raw array paired with its nonnegative
  runtime count, whose refinement relates that count to the storage. The length
  bound is no longer an axiom over arbitrary raw Pulse arrays.
* an index expression `e` in a subscript ⟶ `Pal.Idx ⟦e⟧`, where
  `Idx : (i:Int32.t{Int32.v i >= 0}) -> SZ.t` with `SZ.v (Idx i) == Int32.v i`.
  The side condition `Int32.v i >= 0` is discharged by the bounds obligation of R6.4.
* in *spec* position an index is `Int32.v ⟦e⟧ : nat`, used directly with `Seq.index`.

**R3.4 (structs).** A C# `struct` is a **value**: it has no identity, assignment copies it,
and — unlike a C `struct` — nothing may hold a pointer into the middle of one. That single
fact collapses almost all of PAL's struct machinery. Where PAL emits a record, a ghost
spec type, fold/unfold predicates, per-field pointer projectors and their axioms, a C#
`struct` needs only an F\* record.

A declaration

```csharp
[Refine("P₁")] … [Refine("Pₙ")]
struct S { T₁ f₁; … T_k f_k; }
```

becomes `Struct_S.fst`:

```fstar
noeq type struct_S__raw = { fld_f₁: ⟦T₁⟧; … ; fld_f_k: ⟦T_k⟧ }
let struct_S__pred (this: struct_S__raw) : prop = ⟦P₁⟧ /\ … /\ ⟦Pₙ⟧
type struct_S = this: struct_S__raw { struct_S__pred this }
```

and `⟦S⟧ = Struct_S.struct_S`. Notes, each of which is a decision rather than an accident:

* **Fields are prefixed `fld_`** and always referred to module-qualified (`e.Struct_S.fld_f`),
  so a C# field name can never collide with a Pulse keyword, with another struct's field,
  or with anything in the preamble. By F10 this needs no `open`, which is why a generated
  function module's dependency list never mentions a struct module.
* **The refinement is a refinement type, not a separate obligation to remember.** Anything
  that *produces* an `S` must prove `struct_S__pred`, and anything that *consumes* one may
  assume it — which is exactly what `[Refine]` means, and it falls out of F\* subtyping
  with no work from the emitter.
* **A refinement is bound with the struct's fields in scope as simple names.** `[Refine("Lo <= Hi")]`,
  not `[Refine("this.Lo <= this.Hi")]`: inside a C# `struct` declaration an unqualified
  `Lo` already means "this instance's `Lo`", so this is the reading a C# programmer expects,
  and it lets the shim of §4 be an ordinary static method whose parameters are the fields.
  `this` is a C# keyword and cannot be a shim parameter, so PAL's spelling is unavailable
  even if it were wanted.
* `struct_S__pred` is emitted even when there are no `[Refine]`s, as `True`. Uniform output
  beats output with fewer moving parts in one case and more in another (§0 rule 2).
* **A field's type must itself be translatable and must be a value.** Scalars and other
  translated structs qualify. A reference-typed field — an array, or a class — does not,
  because it would make the struct own a resource, and a value carrying a resource needs
  the separation-logic predicate and fold/unfold discipline this rule exists to avoid.
  Rejected as PALCS0511; see §8.5.

**R3.5 (struct expressions).** Three forms, all structure-preserving:

| C# | Pulse |
|---|---|
| `e.f` | `⟦e⟧.Struct_S.fld_f` |
| `new S { f₁ = e₁, … }` | `{ Struct_S.fld_f₁ = ⟦e₁⟧; … }`, every field present |
| `new S()`, `default(S)` | the same literal with every field at its type's zero |

C# guarantees a `struct` is fully initialized at construction, so the emitted literal is
always total: a field the user did not mention is filled with its zero, which is what the
CLR does. `default(S)` on a refined `S` therefore carries a real proof obligation — the
zero value must satisfy the refinement — and that is correct, since a `default(S)` that
violates `[Refine]` is a bug the annotation was written to catch.

**R3.6 (struct assignment).** `x.f = e` where `x` is a local or `ref` parameter becomes a
whole-value update of `x`'s cell, because that is what a C# field assignment on a value
type *is*:

```
let t = !var_x;
var_x := { t with Struct_S.fld_f = ⟦e⟧ };
```

The deref is let-bound rather than written inline because a record update's source must be
a pure term (F11). Nested paths compose the same way: `x.f.g = e` updates `f` with an
update of `g`.

### 3.4 Classes

**Status: implemented.** Every rule below was written before the emitter, per §0, and every
shape is pinned by `test/pulse_facts/ObjectFacts.fst`, which verifies against the pinned
toolchain. `test/counter_class`, `test/counter_client` and `test/stack_class` are the
acceptance tests.

A class is the construct M1 could not express at all. R3.4 forbids a struct field of
reference type (PALCS0511) because copying the struct would duplicate ownership, which is
why `test/circular_buffer` has to pass its storage array *alongside* the struct that
describes it. A class is a heap cell rather than a value, so it can own its array outright.

**R3.7 (class representation).** A `sealed class C` emits a record of its fields, using the
same `fld_` prefix and the same access and update rules as a struct (R3.5, R3.6):

```fstar
noeq type class_C__raw = { fld_f₁: T₁; … }
```

Unlike R3.4, a field of reference type is **allowed** here, and is the point of the whole
construct.

**R3.8 (class reference type).** `C` is translated to `Pulse.Lib.Box.box class_C__raw`.

`Box` and not `Pulse.Lib.Reference.ref`: `Reference.alloc` carries
`[@@deprecated "Reference.alloc is unsound; only use for model implementations"]` and may
not appear in generated code, whereas `Box.alloc` is an ordinary specified operation
(F14).

**R3.9 (object model).** Each class has a **pure ghost model type**, and the invariant's
job is to relate the implementation type to it.

The model type is **declared by the user**, not derived by the emitter. It is whatever type
the class's `[Model]` member returns — a `Seq<T>`, or a spec-only struct — so it may be a
type the user already has a theory about, and pure lemmas about the model can be stated and
proved without mentioning the implementation at all. The emitter names it `model_M` after
that type; it never invents one.

The one constraint is that the model must expose everything a **caller** needs, both to
establish a precondition and to exploit a postcondition. This is a real constraint, not
bookkeeping: modelling a bounded stack by its element sequence alone leaves capacity trapped
inside the invariant's existential, so a client could not state "the stack is not full" and
`Push` would be uncallable. That stack's model is `{ elems: Seq.seq T; capacity: nat }`.

**R3.9a (spec-only structs).** `[Spec]` on a `struct` declaration makes it a *spec-only
type*: it is erased, it never appears in executable code, and — unlike an ordinary struct
(R3.4) — its fields may be spec-only types such as `Seq<T>` and `SpecInt`. It may still not
own a resource: an array or class-typed field is PALCS0511 here as it is there, because a
ghost value cannot be an owner either.

This is a new requirement that R3.9 forces, not a convenience. The built-in spec-only types
of §8 are all atomic, so without a way to *declare* one there is no way to write a model
that is a product — and a bounded container's model is exactly a product of its contents
and its capacity. `[Spec]` is reused rather than a new attribute introduced because it
already means "exists only in specifications" on a method, and this is the same meaning on
a type.

**R3.9b (the abstraction relation is inlined, bounds first).** The relation between
representation and model is a **conjunct inside the invariant**, not a separate
`abs : raw → model` function.

This is forced rather than stylistic. The abstraction is *partial*: for the stack,
`Seq.slice contents 0 (I32.v top)` is well-typed only once `0 <= I32.v top <= Seq.length contents`
is known. Factoring it out as a total function would mean refining its arguments, and that
refinement would then have to be discharged at **every** use of the model — the identical
trap R4.6 and `test/insertion_sort_sorted` already recorded for `[Spec]` predicates
carrying a `[Requires]`. Inlining costs nothing, because `p₁ /\ p₂` type-checks `p₂` with
`p₁` in scope, so the bounds conjuncts make the partial operation well-typed exactly where
it appears. **Conjunct order is load-bearing**, as it already is for `[Ensures]`.

**R3.9c (`[Spec]` members are functions of the model).** A `[Spec]` member of a class
translates to a pure function of `model_M`, never of `class_C__raw`.

This is what makes `[Requires("Count < Capacity")]` mean anything to a caller: the caller
holds `class_C__inv this m` and nothing else, so every observation a contract mentions must
be computable from `m` alone. A `[Spec]` member whose body reads a field directly is
**PALCS0523**, and its message is "widen the model" — which delivers the diagnosis for the
too-weak-model problem at the *declaration*, rather than as an unprovable call site much
later. The `[Model]` member is the sole exception: reading the fields is precisely its job.

**R3.9d (where a fact goes: `[Invariant]` or `[Refine]`).** The invariant's abstraction
conjunct (R3.9b) is what connects the memory-resident fields to the model, and it is
**mandatory** — it is derived from `[Model]`, and the user does not choose whether to have
it. There is no decision there. What *is* a decision is where each **additional** fact goes,
and it is settled by what the fact mentions:

| The fact mentions | It goes in | Because |
|---|---|---|
| fields (`0 <= top`, `top <= items.Length`) | `[Invariant]` on the class | it is temporarily false between two field writes, so it needs the `unfold`/`fold` window of R4.10 |
| only the model (`Count <= Capacity`) | `[Refine]`, on the `[Model]` member or on the model type | it is a property of a pure ghost value, so it is never breakable — and a caller can only ever see it there |

The second row is not a preference; it is forced by **F17**. A caller holds
`class_C__inv this m` and nothing else. A model-level fact sitting inside that predicate
cannot be reached without unfolding — and once R3.9's deferred `.fsti` step makes the
predicate opaque, cannot be reached at all. Stated as a refinement it travels in the *type*
of `m`, so it arrives with the model, everywhere, for free. This is covered by
`client_sees_model_invariant` in `test/pulse_facts/ObjectFacts.fst` and the generated
translation of `CounterClient.ValueIsNonNegative` in `test/counter_class`.

So each class emits a **refined model type**, in R3.5's shape verbatim:

```fstar
let class_C__model__pred (m: <the [Model] member's return type>) : prop = <the [Refine] clauses>
type class_C__model = m: <the [Model] member's return type> { class_C__model__pred m }
```

and `class_C__inv` is indexed by `class_C__model`. Three details are deliberate.

* It is emitted **unconditionally**, with the predicate `True` when there are no clauses —
  the same reason `struct_S__pred` is emitted when trivial (§0 rule 2).
* It is named after the **class**, not after the model type. This is what lets an *atomic*
  model such as `SpecInt` or `Seq<int>` carry a refinement at all: there is no user-declared
  struct to put one on. Naming it after the model type would also collide whenever two
  classes share one. Verified for the atomic case by `test/counter_class`.
* It **composes with**, rather than replaces, R3.5. When the model is a `[Spec]` struct, a
  fact intrinsic to the type is better placed on the struct itself, where it is simply an
  ordinary struct refinement and is shared by everything using that model; `[Refine]` on
  `[Model]` is for a fact this *class* guarantees. Both shapes are verified — the struct form
  by `test/pulse_facts/ObjectFacts.fst`, the member form by `test/counter_class`.

In a `[Refine]` on the `[Model]` member the model value is named `Result`, as it is in an
`[Ensures]`; in a `[Refine]` on a struct, fields are named directly, as R3.5 already
specifies.

The obligation this creates is discharged where it belongs: at the `fold` of R4.11a, the
emitter must show the model it constructs from the post-state satisfies the refinement. That
is a real proof obligation, and it is what ties the two kinds of fact together — the
representation-level `[Invariant]` is exactly what makes the model-level `[Refine]` provable.

Consequently an `[Invariant]` clause that mentions no field — only `[Spec]` observations — is
**PALCS0527**, advising that it move to the model. This is the same shape of diagnosis as
PALCS0523: a specification-strength mistake reported at the declaration, rather than as an
unprovable call site much later.

**R3.10 (object invariant).** Each class emits
```fstar
let class_C__inv (this: class_C) (m: model_M) : slprop =
  exists* (r: class_C__raw) … .
    B.pts_to this r ** <the resource of each reference-typed field> **
    pure (<bounds> /\ <the model agrees with the representation> /\ <the [Invariant] clauses>)
```

Two properties of this shape are load-bearing.

* **The invariant is indexed by the model, and must be.** With an un-indexed
  `inv (x: C) : slprop`, the object's entire state sits under an existential, so a
  postcondition can mention arguments and nothing else — `Count(this) == Old(Count(this)) + 1`
  would be inexpressible, and every method spec would degrade to "the object is still well
  formed". That is memory safety, not functional correctness, and it is exactly the
  weak-specification failure this project exists to avoid. The index is what makes
  functional correctness statable. Note that this is not a new idea here: `A.pts_to var_a s`
  is already a model-indexed resource, and R4.10 threads a class's model exactly as R4.4
  already threads an array's.
* **A class invariant is a `pure` conjunct inside the predicate, not a `[Refine]`.** A
  refinement type must hold of *every* value of the type, but R3.6 writes a whole record
  per field assignment, so a method that transiently breaks its invariant between two field
  writes would be rejected outright. Struct refinements are always true; class invariants
  are temporarily breakable, and the fold/unfold discipline of R4.10 is what marks the
  window in which they may be broken. Using one mechanism for both would be wrong. This
  concerns the **representation** only; a fact about the model alone must go the other way,
  as a refinement on the model type, for the reason R3.9d and F17 give.

**R3.10a (a class owns its arrays).** For each field of array type, the invariant gains an
existential for its contents, an `A.pts_to` conjunct, and a length bound:

```fstar
let class_C__inv (this: class_C) (m: class_C__model) : slprop =
  exists* (r: class_C__raw) (contents_f: Seq.seq ⟦T⟧).
    B.pts_to this r **
    A.pts_to r.fld_f contents_f **
    pure (Seq.length contents_f <= 2147483647 /\ … )
```

This is the rule R3.4 could not have. A struct is a value, so a field owning a resource
would make every copy a second owner (PALCS0511) — which is why `test/circular_buffer` has
to pass its storage *alongside* the struct describing it, leaving the two connected only
by a convention the type system does not enforce. A class is a heap cell with identity, so
there is exactly one owner and the array can go inside. The consequence is that the
storage becomes genuinely private: a client never names it and, by F16's linearity, cannot
alias it.

Three details are forced.

* **The field name denotes the *contents* in every specification, and the reference only in
  the `A.pts_to`.** `items.Length` is `Seq.length contents_items` and `Pal.Contents(items)`
  is `contents_items`, so a class-level clause reads exactly as a method contract about an
  array parameter already does (R4.4). Nothing new has to be learned to write one.
* **The length bound is emitted for every array field.** It is a fact about the C# type —
  an array's length is an `int` — and not an assumption: it enters at `new T[n]`, whose
  argument is already an `int`, and is re-proved at every fold from there. It is stated
  first because it is what makes arithmetic on an index into the array provably
  non-overflowing: `top < items.Length` bounds `top + 1` only once `items.Length` is known
  to be bounded.
* **A field of *class* type is R3.10b's business**, and the same shape.

The obligation this creates lands at the `fold` of R4.11a, and needs one extra device
there. After a method has written into the array, the contents the `unfold` produced are
stale, and the emitter never named the new ones. `with c. assert (A.pts_to …f c);` binds
them — the same device R4.14 needs, for the same reason.

**R3.10b (a class owns its objects).** For each field of class type the invariant gains an
existential for the sub-object's **model** and a conjunct holding the sub-object's own
invariant:

```fstar
let class_C__inv (this: class_C) (m: class_C__model) : slprop =
  exists* (r: class_C__raw) (model_g: Class_D.class_D__model).
    B.pts_to this r **
    Class_D.class_D__inv r.fld_g model_g **
    pure (… /\ m == ⟦abstraction⟧)
```

This is R3.10a with one word changed. An array field contributes its *contents*; an object
field contributes its *model*; in both cases the field's **reference** appears only in the
resource, and the field name denotes the summary everywhere in the `pure`. So
`low.N` in an `[Invariant]` is `spec_D_N model_low`, which is what `low.N` means in a
client's contract about an object parameter. One reading of a member access, everywhere.

Four things follow.

* **The outer invariant contains the inner one; it does not restate it.** An inner class's
  `[Invariant]` clauses are proved once, where they were written. What the outer class adds
  is what only it can say — a clause relating two sub-objects, such as `low.N <= high.N`.
  That is what composition is *for*, and it is the reason the sub-model rather than the
  sub-object is what the invariant quantifies: a fact about two objects has to be a fact
  about two values.
* **Inside R4.10's window the sub-object is still folded** (F20). The window opens the
  outer box; it does not open what the box holds. So `low.Bump()` in a method of `Range` is
  an ordinary call, needing `Counter`'s precondition and nothing else — and it is *not* a
  self-call, because the receiver is a different object. The question the old refusal said
  the scheme could not answer — when may the outer object open the inner one? — turns out
  not to arise: it never opens it.
* **How an owner names a whole sub-model** is the existing `[Spec]` mechanism doing an
  extra job. A `[Spec]` member of `D` returning `D`'s model type makes `low.State` mean
  `spec_D_State model_low`, so a composite model can hold sub-models rather than
  re-projecting each scalar. No new annotation was required.
* **A bound on a sub-model must be a `[Refine]` on the sub-class's `[Model]`.** F17 is not
  optional here: at a call site the sub-invariant is a folded slprop, so a `pure` conjunct
  inside it is not in the context, and `low.N <= 2147483647` will not be available to
  discharge `Bump`'s precondition. The refinement travels with the model type and is
  therefore always in scope.

The `fold` needs the same extra device R3.10a's arrays need, and for the same reason: a
method may have called something that moved a sub-model, so the binder the `unfold`
produced is stale. `with model_g. assert (Class_D.class_D__inv …fld_g model_g);` names
what the context is actually holding.

Three consequences of the rule being *the same* rule are worth stating, because each was
a question the refusal left open, and `test/deep_class` settles all three.

* **A class may own an array and an object at once**, and nothing mediates between them.
  `Ledger` writes `slots[at]` and then calls `cursor.Step()`; the write settles nothing
  about the cursor and the call settles nothing about the array, which is separation and
  not a rule anyone had to add. The invariant may relate them — `cursor.Bound ==
  slots.Length` ties the object to the array's length — because by then both are values.
* **Depth is not a special case.** `Ledger` owns a `Cursor` that owns two `Cell`s, and the
  middle level is a composite and a component at once. A client of `Ledger` reasons about
  a sequence and a count and never learns that the count lives in a `Cell`.
* **Refinements do not inherit, so each level republishes what its owners need.** A
  `[Refine]` belongs to the *class* model type `class_D__model`; an owner's composite model
  is built from the `[Spec]` **struct** `struct_DModel`, which is that type without the
  refinement. So `Cell`'s `0 <= V` is available inside `Cursor`'s window and *not* in
  `Ledger`'s contracts, and `Cursor` has to state it again. This is F17 one more time, and
  it is the one cost R3.10b charges for depth. It is not busywork: the facts a level
  publishes are exactly the facts its clients may use, so restating them is the interface
  being written down. The alternative — refining the composite's field types by the owning
  class — is not available, because a `[Spec]` struct names no class and several classes
  may share one.

**Ownership transfer is not expressible, and Pulse says so.** A class-typed *parameter* is
preserved (R4.9), so a constructor that stores one in a field asks the `fold` for a
resource its own postcondition also returns, and Pulse reports `Cannot prove:
class_Cell__inv var_x pre_x`. That is the same disposition as a self-call: the translation
is faithful, the program is wrong, and the prover is the one to say it. Sub-objects are
therefore built by the constructor that owns them, which is also why no owner can alias
two of its fields. Aliasing at a *call* is the same disposition again — see R3.13.

What is *still* PALCS0531 is a field whose type is spec-only — a `Seq`, a `Ghost`. Those
are mathematical values with no runtime representation and no resource, so there is nothing
for the invariant to hold and nothing for a constructor to allocate. A field of a class
that declares no `[Model]` is **PALCS0500**, with a message saying so: it fails the type
map rather than the ownership rule.

**R3.10c (the invariant is indexed by a permission).** Every class invariant takes a
**meta-argument-defaulted** permission binder, and the permission propagates to every
resource conjunct — the box, each array field, and each sub-object's own invariant:

```fstar
let class_C__inv (this: class_C) (#[T.exact (`1.0R)] p: perm) (m: class_C__model) : slprop =
  exists* (r: class_C__raw) (contents_f: Seq.seq ⟦T⟧) (model_g: Class_D.class_D__model).
    B.pts_to this #p r **
    A.pts_to r.fld_f #p contents_f **
    Class_D.class_D__inv r.fld_g #p model_g **
    pure (…)
```

`class_C__inv this m` still *means* `class_C__inv this #1.0R m` (F21), so this rule changes
no other rule's output: full ownership is what you get by not asking for anything, which is
what every existing contract says. The whole feature is reached by asking.

Three things about the shape are forced.

* **The propagation is uniform, and it has to be.** A fraction that stopped at the box
  would let two observers of one object disagree about its array, which is exactly the
  unsoundness the box's fraction was preventing. An object at permission `p` is an object
  every part of which is held at `p`; there is no other coherent reading, and it is why
  `[Frac]` on a *field* is not a thing the language offers. A field's permission is the
  enclosing invariant's, always.
* **The model index is unaffected.** A fraction weakens what you may *do* with the object,
  not what you may *know* about it: an observer still names `this.Count` and still gets a
  postcondition about it. That is the point of separating the model from the
  representation — the model was never ownership in the first place.
* **The permission is not part of the model.** Nothing in a `[Model]`, an `[Invariant]` or
  a contract can mention `p`; it is a binder the translation introduces and the user names
  only through `[Frac]`. A specification that could talk about its own permission would be
  talking about the proof rather than the program.

**R3.10d (share and gather).** Each class additionally emits three ghost lemmas:

```fstar
ghost fn class_C__inv_share (this: class_C) (#p: perm) (#m: class_C__model)
  requires class_C__inv this #p m
  ensures  class_C__inv this #(p /. 2.0R) m ** class_C__inv this #(p /. 2.0R) m

[@@allow_ambiguous]
ghost fn class_C__inv_gather_gen (this: class_C) (p q: perm) (#m #m': class_C__model)
  requires class_C__inv this #p m ** class_C__inv this #q m'
  ensures  class_C__inv this #(p +. q) m ** pure (m == m')

[@@allow_ambiguous]
ghost fn class_C__inv_gather (this: class_C) (#p: perm) (#m #m': class_C__model)
  requires class_C__inv this #(p /. 2.0R) m ** class_C__inv this #(p /. 2.0R) m'
  ensures  class_C__inv this #p m ** pure (m == m')
```

They are emitted per class rather than written once in the support library because their
proofs recurse into the class's own structure: `share` shares the box, then each array,
then calls **each sub-object's `share`** (F22). A generic lemma would have to quantify over
that structure, and there is nothing to quantify over — the invariant is a `let`, not an
instance of an interface.

Six details are forced, and each was found by a probe rather than assumed.

* **Every `fold` in the proofs is preceded by an `assert` naming what it consumes** (F22).
  The invariant's existentials are solved by matching against the context, and after a
  share the context holds two candidates for each of them. This is the emitter emitting
  the *scheme*, not rescuing a proof: the lemma's body is fixed by the rule and does not
  vary with the program, exactly as R4.10's fold/unfold bracket does.
* **`gather` proves the two models equal** (F23), and that is not an extra hypothesis. R3.9
  pins `m` to the abstraction function of the representation, `Box.gather` proves the two
  representations equal, and a function of equal arguments is equal. Two read-only aliases
  of one object *necessarily* agree about it — which is the entire reason to allow them.
  A scheme in which they could disagree would be one in which the model was not an
  abstraction function, and F17 already rules that out.
* **`gather` is stated as `share`'s exact inverse**, with the general form kept alongside
  it. Pulse normalises `p /. 2.0R +. p /. 2.0R` to `p` for `pts_to` but not for a
  user-defined slprop (F24), so without this the arithmetic would surface as a `rewrite`
  the user had to write at every call site — a proof step about the *encoding*, which is
  precisely what a proof annotation language must not make anyone write. Discharging it
  once, inside the emitted lemma, is the alternative.
* **`gather_gen` takes its two permissions as *explicit* parameters**, and `gather` calls
  it as `class_C__inv_gather_gen this (p /. 2.0R) (p /. 2.0R)`. Left implicit they are
  solved by matching, and a *nested* gather could then return at `q +. p` where its
  caller's `fold` wanted `p +. q` — the same permission, but a user-defined slprop gets no
  normalisation (F24) and matching is syntactic. Naming them at the call site fixes the
  order once and the nesting composes. Nothing one level deep can detect this, which is
  why F23's pin is a class owning a class.
* **The second view is renamed onto the first *before* anything is gathered**, using
  `Box.pts_to_injective_eq` rather than `Box.gather`. `gather` is `allow_ambiguous` and its
  `ensures` keeps whichever of the two values it matched first, so a subsequent `fold`
  naming the other one fails against a resource provably equal to what it asked for.
  Learning `r == alt_r` without consuming either view, and rewriting first, leaves exactly
  one candidate for every existential — after which the closing `fold` needs no `assert`
  at all, because there is nothing left to disambiguate.
* **A class with no `[Model]` gets none of them**, because it has no invariant to share.

**R3.10e (`share` needs no permission left over).** Nothing bounds how far a permission may
be split: `share` halves whatever it is given, and halving is always possible. The only
thing a program can never do is *write* through a fraction — a write needs `1.0R`, which no
proper fraction can reach and which `gather` recovers only by collecting every piece back.
That asymmetry is fractional permissions working, not a limitation of the translation, and
it is what makes read-only aliasing safe to allow where R3.13's aliasing was not.

What *is* bounded is how many views may be live at once, and the bound is **two** (F27).
Matching an slprop against the context is a search for a unique candidate, so a second
`Share` on a name that already has two views leaves three resources with the same head and
the same name, and the next call is refused — with an error that lists the very thing it
wanted, three times over. More than two observers is reached by nesting: `Share`, use both
halves, `Gather`, and only then `Share` again.

This is worth being precise about, because it is a fact about Pulse's matcher and not about
permissions, and the two are easy to confuse. The permission really does split arbitrarily
far; `test/pulse_facts`'s `frac_split_thrice` halves twice and recombines twice with nothing
in between. It is *simultaneity* that is limited, and pal-csharp says nothing about it —
the refusal arrives from Pulse, on the C# call site, through R2.3.

**R3.11 (null).** `Box` already models a nullable CLR reference, so `null` needs no new
machinery: `Box.null` is `null`, `Box.is_null` is a *pure* boolean (so it may appear in a
contract), and `Box.pts_to_not_null` proves that a live object is non-null.

That last one settles the design. Ownership *implies* non-nullness, so a method holding
`class_C__inv this m` never has to test for null and R6.4's "no null dereference"
obligation is discharged by the invariant rather than by a check. `C?` maps to `box` with
no additional obligation; `C` maps to `box` together with a `pure (not (is_null x))`
conjunct that `pts_to_not_null` supplies for free.

**R3.12 (allocation and the garbage collector).** `new C(…)` emits `Box.alloc`, and the
emitter **never** emits `Box.free`.

This needs no MODELING AXIOM. Pulse slprops are affine: `Box.free`
exists but nothing compels a caller to reach it, and a leftover resource is discharged by
`drop_` (F15). An object whose invariant is simply dropped *is* a garbage-collected object.
`Pulse.Lib.CSharp.Array.alloc` likewise uses verified `Vec.alloc` and transfers its
ownership to the length-carrying wrapper. Generic empty allocation remains a separate
trusted operation; see [the soundness campaign](soundness-campaign.md). The CLR
being garbage collected is thus a genuine simplification over PAL's C, not merely a
different set of obligations.

**R3.13 (aliasing).** An object resource is linear, so two owned parameters are necessarily
distinct objects. Aliasing is therefore not unsound — it is *unprovable*, and Pulse is what
says so: `Merge(s, s)` gets `Cannot prove: class_C__inv var_s _`.

This rule used to say the opposite. The emitter detected a call passing syntactically equal
object arguments to two owned parameters and refused it as `PALCS0520`, on the reasoning
that F*'s message means nothing to someone who has just written `Merge(s, s)` and that a
diagnostic is not a proof step, so §0 rule 3 was untouched. The reasoning was wrong in two
ways, and both are worth keeping written down.

*It put a rule about separation logic in a pass that does not do separation logic.* The
check could see `f(a, a)` and nothing else. It could not see `f(a, a.Inner)`, or an alias
established three statements earlier, or two paths to one object through a field — all of
which are the same mistake and none of which it caught. So it was never the rule; it was a
syntactic silhouette of the rule, and the difference between those is exactly where a
frontend starts lying. §0 rule 3 says the emitter never invents a proof step. The same
rule points the other way too: **the checker never invents a refusal.** What pal-csharp
refuses is what it cannot *translate*. What Pulse refuses is what cannot be *proved*, and
that boundary is the only reason the frontend is small enough to trust.

*And a refusal hides everything behind it.* `test/diagnostics/cases/AliasedObjects.cs`
carried a second bug for as long as it existed — its `Transfer` required a bound on `from`
while depositing into `to`, so the method did not verify on its own account. Nobody found
out, because the file was refused before it was ever emitted. A frontend that answers
questions the verifier should answer does not merely answer them worse; it stops the
verifier from being asked.

What remains true is the original complaint: `Cannot prove: class_C__inv var_s _` is a poor
thing to show a C# programmer. That is a problem about *where the message appears*, not
about who should produce it, and R2.3 is how it is solved — the message is F*'s, reported
on the C# line that caused it. The case now lives in `test/pulse_refusals`, which checks
all three things at once: that the translation is clean, that Pulse refuses it for the
stated reason, and that the refusal lands on the line the reader is looking at.

---

## 4. Methods and contracts

**R4.1 (method).** A static method

```csharp
[Requires(P₁)] … [Ensures(Q₁)] …
static R M(p₁, …, pₙ)   { B }
```

emits

```
fn func_M (var_p₁: ⟦T₁⟧) … (var_pₙ: ⟦Tₙ⟧) (#g₁: erased ⟦G₁⟧) …
requires ⟦own(p₁)⟧ ** … ** pure (⟦P₁⟧ /\ …)
returns  var_result: ⟦R⟧
ensures  ⟦own'(p₁)⟧ ** … ** pure (⟦Q₁⟧ /\ …)
{ ⟦B⟧ }
```

The ownership conjuncts come from R3.2 and the pure conjuncts from the user's annotations,
in source order. The emitter contributes **no** additional pure conjuncts beyond the
obligations of §6. A method with no parameters at all takes the single binder `()`, since
a Pulse `fn` must have one (F12).

**R4.2 (parameter rebinding).** Every by-value parameter that the body assigns to is
rebound as `let mut var_p = var_p;`, as PAL does. Parameters that are never assigned are
used directly.

**R4.3 (`Old`).** `Old(e)` in an `ensures` denotes `⟦e⟧` evaluated against the `requires`
state: the emitter binds the pre-state existentials once and refers to them. `Old` is
illegal outside a postcondition.

**R4.4 (`Result`).** In an `ensures`, `Result` denotes the `returns` binder `var_result`.
A C# parameter or local named `result` is translated as `var_result'` so that it cannot
be captured by the binder; a prime cannot occur in a C# identifier.

**R4.6 (`[Spec]` methods).** A `[Spec]` method is pure, ghost, and
usable *only* in specification position. Consequently its C# parameter types are
translated with the **spec** reading rather than the code reading:

| C# parameter of a `[Spec]` method | Pulse binder |
|---|---|
| `int`, `long`, … | mathematical `int` (no overflow obligations arise in specs) |
| `T[]`, `Span<T>` | `Seq.seq ⟦T⟧` — the contents, not the array |
| `bool` return | `prop` |

Its `[Requires]` clauses become a **refinement on the last binder**, so that the body
type-checks: `Sorted`'s `hi <= a.Length` is what makes `Seq.index var_a var_j` well-typed
under the quantifier in its body. Correspondingly, at a call site in spec position an
argument of C# type `int` is translated as `Int32.v ⟦e⟧`, and an array argument as its
contents existential.

**R4.5 (ghost parameters).** A parameter of type `Ghost<G>` (necessarily optional, so C#
callers may omit it) emits an erased implicit `(#g: erased ⟦G⟧)` and is erased from the
runtime signature. Equivalently `[GhostArg("G g")]`.

*Known limitation, shared with PAL.* An implicit binder is resolved by unification at the
call site, so a ghost argument that appears only in the **pure** part of a contract is not
determined and such a method cannot yet be called from translated C#. Ghost arguments that
appear in a separation-logic conjunct are resolved from the resource and call normally.

**R4.7 (`[Lemma]` methods).** A lemma is a proof step about the values the program
actually holds, so — unlike a `[Spec]` function (R4.6) — its parameters keep their
**program** reading: `int` is `I32.t`, `SpecInt` is `int`, `T[]` and `Seq<T>` are
`Seq.seq`. It is emitted as an ordinary F\* lemma in `Let_C_L.fst`,

```
let lemma_C_L (var_p₁: ⟦T₁⟧) … : Lemma (requires ⟦P⟧) (ensures ⟦Q⟧) = ⟦body⟧
```

where `⟦body⟧` is the C# body, the `[PulseBody]` text with `$(…)` antiquotation expanded,
or `admit()` under `[Admit]`. A call is a plain ghost statement `Let_C_L.lemma_C_L a₁ … aₙ;`
with the arguments passed **raw** — no `Int32.v` coercion, because the lemma's binders are
already program-typed. A lemma that wants a mathematical index therefore declares `int n`
and lets the specification translation insert `I32.v` where the *specification* needs it.

**R4.8 (postconditions are stated under the precondition).** A Pulse `ensures` is
type-checked in a context that does **not** include the `requires`, so a postcondition
whose well-typedness depends on the precondition — `Result == s[i]` guarded by
`i < s.Length` is the everyday case — would be rejected before any proof is attempted.
The emitted postcondition is therefore

```
ensures … ** pure ((⟦P₁⟧ /\ … /\ ⟦Pₙ⟧) ==> (⟦Q₁⟧ /\ … /\ ⟦Qₘ⟧))
```

This weakens nothing. The precondition is expressed entirely over pre-state binders, which
remain in scope in the postcondition, and the caller has just discharged it, so
`P ==> Q` gives the caller exactly `Q`.

It does **not** rescue a postcondition whose well-typedness depends on an *earlier
postcondition*; F\* type-checks each conjunct of `p₁ /\ p₂` with `p₁` in scope, so the
conjunct that bounds an array must be written before the conjunct that indexes it. That is
an ordering obligation on the annotations, and it is documented rather than inferred.

**R4.9 (fractional permissions).** `[Frac("p")]` on an array or `ref`/`in` parameter
introduces a ghost permission binder `(#p: perm)` and weakens the parameter's resource
from full ownership to `A.pts_to a #p s` (resp. `R.pts_to x #p v`). Two consequences follow
mechanically, and neither is a choice:

* **The contents cannot change**, so the *same* binder stands for the pre- and the
  post-state. The `ensures` needs no existential for that parameter and the caller needs no
  frame reasoning about it. Compare the full-ownership case (R4.1), where every array
  parameter contributes an existential to every postcondition.
* **Writing through the parameter is an error** (`PALCS0305`), reported against the
  assignment. A fractional permission is exactly the right to read.

What this buys, and what nothing else does: the same array may be passed to two parameters
at once — provided the caller splits its permission first, which is `Pal.Share` (R5.13).

**R4.9a (an observed object).** `[Frac("p")]` on a **class-typed** parameter weakens its
resource the same way, from `class_C__inv a m` to `class_C__inv a #p m`:

```csharp
public static bool SameSize([Frac("pa")] Stack a, [Frac("pb")] Stack b) => …
```
⟶
```
fn func_Cmp_SameSize (var_a: Class_Stack.class_Stack) (var_b: Class_Stack.class_Stack)
                     (#pa: perm) (#pb: perm)
                     (#pre_a: erased Class_Stack.class_Stack__model)
                     (#pre_b: erased Class_Stack.class_Stack__model)
  preserves Class_Stack.class_Stack__inv var_a #pa pre_a
  preserves Class_Stack.class_Stack__inv var_b #pb pre_b
  …
```

The consequences are R4.9's, one word changed, and one of them is new.

* **The model cannot change**, so — as for an array — the one binder stands for the pre-
  and the post-state. An observed object contributes no existential to the postcondition,
  which is why `SameSize`'s `ensures` can say `Result == (a.Count == b.Count)` with no
  `Old` and no frame reasoning.
* **The two permissions are independent binders**, which is exactly what makes `a` and `b`
  allowed to be the same object. Giving both parameters one binder would forbid it again
  by construction.
* **A mutating method may not be called on it**, and pal-csharp does not say so — Pulse
  does, because `Push` requires `class_Stack__inv this m` and the context holds
  `class_Stack__inv this #p m`. This is §0 rule 3's other direction working as intended:
  the frontend would have to know which methods mutate, which is a question about
  contracts, and the contracts are already in front of the prover.

### 4.5 Instance methods

**R4.10 (instance method).** An instance method of `sealed class C` translates exactly as
R4.1 does, with three additions. The receiver becomes a leading explicit binder `this`, the
model becomes a leading *erased* implicit binder, and the object resource brackets the
contract:

```csharp
[Requires(P)] [Ensures(Q)]
public void M(T x) { … }
```
⟶
```
fn method_C_M (this: class_C) (var_x: ⟦T⟧) (#m: erased model_M)
  requires class_C__inv this m ** pure ⟦P⟧
  ensures  exists* m'. class_C__inv this m' ** pure ⟦Q⟧
{ unfold class_C__inv this m;  ⟦body⟧;  fold class_C__inv this <the new model>; }
```

The postcondition **existentially quantifies the new model** `m'` and constrains it with
the user's `[Ensures]` clauses, read over `m'` and `m`. It does *not* name the new model as
an emitter-computed function of the old one: there is no way to compute a model transformer
in general, and inventing one would be exactly the proof step §0 rule 3 forbids. This is
also the shape arrays already use — `ensures exists* post_a. A.pts_to var_a post_a ** pure (…)`
— so a class's model is threaded precisely as an array's is (R4.4), and `Old` needs no new
machinery: inside ⟦Q⟧ an observation reads as `spec_C_Obs m'`, and `Old(observation)` as
`spec_C_Obs m`.

*A self-call is a call like any other.* An instance method called on `this` lowers, by
R6.6, to a call whose first argument is `this` — because that is what it is. Its precondition asks for
`class_C__inv this m`, and the window this method is running in is precisely where that
does not hold, so **Pulse reports it**. The emitter neither refuses it nor arranges around
it, and both restraints are deliberate.

Refusing would be a claim the scheme is not entitled to make. The rule is a consequence of
R4.10, not an extra restriction on top of it: an unfolded object does not satisfy a
contract that asks for a folded one, and Pulse says so in exactly those terms. A
compiler-side check would be a *second*, hand-maintained statement of the same fact,
free to drift from the first.

Arranging around it would be worse. Re-folding before the call and re-unfolding after is
the obvious repair, and it silently inserts a proof obligation the user never wrote — the
invariant would have to be re-established at a point they did not choose, and when it could
not be, the failure would land there rather than where the design went wrong. That is §0
rule 3's case exactly.

So the remedy is the user's, and it is the ordinary one: move the shared work into a static
method taking what it needs, and have both instance methods call *that*. What is left over
after doing so is usually a sign that the object wanted a state-indexed invariant, which is
a different scheme (see §8).

**R4.10a (the receiver is spelled `@this`).** A contract on an instance member names the
receiver `@this`, as in `[Requires("@this.Count < @this.Capacity")]`.

This is forced by the shim mechanism (§4 of `internals.md`), and both halves were checked
against Roslyn rather than assumed:

* A spec string is compiled as the body of a **static** method, so a bare `this` is
  `CS0026: Keyword 'this' is not valid in a static property, static method, or static
  field initializer`. The receiver must be an ordinary parameter.
* `ShimParameters` already renders every parameter with an `@` prefix, so a parameter
  *named* `this` renders as the verbatim identifier `@this`, which is legal C# and binds.
  Nothing in the shim machinery changes.

`CS0026` inside a spec string is therefore remapped to **PALCS0526**, whose message is
"write `@this`" — the one error every user will hit once.

**R4.10b (a contract may only name accessible members).** The shim lives in
`namespace __PalSpecShims`, so a contract can reference only `public` or `internal` members
of the class: `@this.Priv` on a private member is `CS0122`, remapped to **PALCS0525**.

A `[Spec]` member intended for use in contracts must accordingly be at least `internal`.
`[Model]` is exempt and may be `private`, because it is consumed only by R3.10's invariant,
which the emitter builds from the member's *body* — inside the class, where private fields
are visible. That asymmetry is the point: the abstraction function sees the representation,
and nothing else does.

The `unfold`/`fold` bracket is the window in which R3.10's invariant may be broken.

**R4.10c — the bracket is opened if and only if the body names a field of the receiver,
and a body that names one may not also call a method on it (`PALCS0597`).** (R22.15 has since lifted the second half for a receiver that is not a view: the
receiver is folded around the call.) The bracket
used to be emitted unconditionally, on the §0 rule 2 argument that a uniform shape is
better than a conditional one. That argument was wrong here, because the two things a body
can do with its receiver want *opposite* states:

| the body | wants the invariant |
|---|---|
| reads or writes a field | unfolded — the fields are behind it |
| calls a method on `this` | folded — that is what the callee's contract requires |

A body that only delegates (`int Again() => Get();`, or R9.20's `int Width() => Span;`)
therefore had its receiver opened and then handed a representation to a function expecting
an invariant. That is ill-typed Pulse, emitted with `0 error(s)`. Opening only when a field
is named fixes it, and makes true what this section had always claimed: the bracket goes
where the field accesses are.

A refusal was retired by this rule, which is worth recording because the reasoning that
justified it was correct and the conclusion was still wrong. `test/pulse_refusals` held a
case in which `IncrementTwice` calls `Increment` twice on `this`, and its comment argued
that the frontend should *not* rule on it: the frontend cannot see the prover's context,
Pulse can, and a refusal invented by the checker is as bad as a proof step invented by the
emitter (§0 rule 3, pointed the other way). All of that is true. But the premise underneath
it — that the invariant is open there — was not a fact about separation logic, it was a fact
about this emitter, and the emitter was wrong. The case verifies now, unchanged, and lives
in `test/counter_class`. **When a refusal is justified by what the prover cannot do, check
first that the prover was asked the right question.**

The mixed case cannot be fixed the same way, and is refused rather than approximated.
Closing the bracket around the call and reopening it after would be a proof step the
emitter invented: R4.11a's `fold` must hold of the state at the fold point, and R3.10's
`Shift` is the standing counterexample — its invariant is *false* between its two
assignments, which is the whole reason the bracket exists. §0 rule 3 says the fix belongs
in the annotations, and here it is a small one: read the field through the method, or
inline the callee.

**R4.11 (read-only method).** When a method assigns no field and passes `this` to no
mutating method, R4.10's two clauses collapse to one:

```
preserves class_C__inv this m
```

`preserves p` is a real Pulse spec clause meaning exactly `requires p ensures p`, and it
composes with `requires`/`ensures` (F13). This is a *specification-strength* rule, not an
optimisation, and it is the read-only case that needs it. Under R4.10's existential form a
read-only method says only "*some* model holds afterwards"; the caller loses the fact that
the object is unchanged unless the user writes `[Ensures("@this.X == Old(@this.X)")]` for
every observation. `preserves` states it once, for all of them. The distinction is decided
by a write-set analysis, not by a heuristic.

*What counts as a write*, precisely, because two of the three were learned the hard way:

1. A **field assignment**. The original rule, and the only obvious one.
2. A **write into an array the object owns**. `items[i] = v` assigns no field symbol, but
   R3.10a says the contents *are* part of the model, so a method doing only this moves its
   model and must not be given `preserves`. The test peels an assignment target down to its
   root before asking whether it is a field. Handing an owned array to any callee counts
   too: it may come back written.
3. A **call to an instance method that is not itself read-only**. This one *follows the
   call*, and R3.10b is why it must. An owner reads its state by calling its sub-objects'
   read-only methods, so a rule counting any instance call as a write would classify every
   such reader as a mutator — and its caller would be handed a result related to a model it
   knows nothing about. That is not a conservative approximation, it is a useless answer.
   Recursion terminates by treating a cycle as a write.

Every one of these errs strict when it errs: the permissive direction would tell a caller
the model did not move when it did, which is unsound, while the strict direction only costs
the caller an existential — exactly what it would have had without R4.11 at all.

**R4.11c (`Assigned` is not `Mutated`).** The same three-part test answers a second
question — *which objects in a body have moved by the time the postcondition is stated*, and
which of a loop's objects R5.8b may hold fixed — and it must be the one that answers it.
The tempting shortcut is `Normalize.Assigned`, which is already there; but `Assigned`
answers R4.2, "which names need a mutable cell", where saying yes too often costs a
`let mut` and nothing else. Here it costs the *model*: an object wrongly called mutable is
re-quantified, and a postcondition like `Result == a.TheArea + b.TheArea` becomes
unstateable at the very call site that needs it. The rule therefore lives in exactly one
place, `Normalize.Mutated`, and `Assigned` is never used to answer it. Note also that
"errs strict" reverses here: for a *loop*, holding an object fixed is the strong reading,
so the two consumers need the same precise answer for opposite reasons.

**R4.11b (a read-only method is observed, not owned).** The same analysis decides one more
thing: a method that gets `preserves` also gets a permission binder, and its receiver is
held at that permission rather than at `1.0R`:

```
fn func_C_M (var_this: Class_C.class_C) (#p: perm) (#m: erased Class_C.class_C__model)
  preserves Class_C.class_C__inv var_this #p m
```

No annotation is involved, and none is offered. Three reasons this is inference where
R4.9a is annotation.

* **It is a pure generalisation** (F26). A caller holding full ownership is unaffected:
  Pulse instantiates the binder at `1.0R` and the call site is textually what it was. So
  unlike `[Frac]` on a parameter — which *weakens* what the callee may do and therefore has
  to be the author's decision — this weakens nothing and can be given for free.
* **It is forced by R3.10c** rather than merely allowed. The fraction propagates into
  sub-object invariants, so a read-only method of an owner holds its parts at *its own*
  permission. If a part's readers were fixed at `1.0R`, no fractional owner could read its
  own parts, and R3.10b's composition would stop at the first fraction. Generalising is not
  an optimisation here; it is what makes the two rules compose.
* **It is decided by the same analysis, so it cannot disagree with `preserves`.** A method
  that may move its model needs full ownership and a method that cannot does not, and those
  are the same question asked once. Two analyses could drift apart; one cannot.

That last claim held only for as long as the write set was the *only* way to say
"read-only". R9.7 added a second — `[Frac]` on a method — because an `abstract` method has
no body to analyse, and the two promptly drifted. R4.11c is what stops them.

**R4.11c — one answer about the receiver, and F\* judges it.** `IsReadOnly` *is* the
answer to "does this method own its receiver": `[Frac]` where it is written, the write set
otherwise. Nothing downstream may ask the question a second time. `MethodPlan` did — it
seeded the mutated set from `IsReadOnly` and then let `Normalize.Mutated` re-derive the
receiver from the body — and that is the whole of the defect this rule exists to prevent.

The drift was not visible as a disagreement; it was visible as a *wrong proof*. `[Frac]`
overrides the write set, so on a single class the emitted signature was built mutating from
the body and the annotation meant nothing at all. In a hierarchy it was worse: the
class-level declaration and the vtable slot were built read-only from the annotation while
the body's signature was built mutating from the write set, and the read-only one carried
the user's postcondition with the post-model collapsed onto the pre-model —
`TheBalance == TheBalance + 7`, which is `False`. Nothing caught it but an incidental arity
mismatch in the generated vtable. Had the arities agreed, a caller would have had `False`
in scope. **A duplicated analysis is how an unsound emission gets made; a missing check is
not.**

Once emission is consistent the remaining question — *may a body that writes a field be
verified against a receiver held at a fraction?* — is a separation-logic question, and
Pulse answers it against the body the user wrote: the assignment cannot be proved at
`B.pts_to var_this #p _`. An `override` of a `[Frac]` slot is the same question at the
slot's contract, and fails the same way. `test/pulse_refusals/cases/FracMutates.cs` and
`FracSlotOverride.cs` are the evidence, and they are tests *because* the emission is
consistent: a frontend refusal here would have made the verifier's answer untestable.

This was briefly such a refusal, **PALCS0551**, and it was a regression against a principle
this repository had already written down — see `test/pulse_refusals/run.sh`, and
`cases/AliasedObjects.cs` for **PALCS0520**, removed for the same reason and uncovering a
bug it had been hiding. §0 rule 3 reads both directions: the emitter never invents a proof
step, and the checker never invents a refusal.

What this rule does **not** do is decide anything about a *call*. Whether a caller has
enough permission for the method it is calling is a separation-logic question, and R3.13's
lesson applies: it is asked and answered by Pulse, against the contracts, and the answer
arrives on the C# call site through R2.3.

**R4.11a (fold witness).** R4.10's closing `fold` must name the model it re-establishes,
and the term to name follows from the same write-set split:

| Method shape | `ensures` clause | `fold class_C__inv this …` at |
|---|---|---|
| assigns no field (R4.11) | `preserves class_C__inv this m` | `m` — the pre-state model binder |
| assigns a field (R4.10) | `exists* m'. class_C__inv this m' ** …` | ⟦*body of* `[Model]`⟧, evaluated at the post-state |

Each is forced, and neither is a search. In the read-only case the representation is
untouched, so `m` is still a correct index and is the *only* term that discharges
`preserves` — refolding at a recomputed model fails with `Error 228: Cannot prove:
class_C__inv this m`, because reconciling two indices is a matching problem the prover does
not hand to the SMT solver. In the mutating case `m` is stale and the new model is not yet
named by anything, so the emitter re-reads the representation and applies the abstraction:
this is not an invented proof step but the *definition* of the model, the one the user
supplied in `[Model]` (R3.9), transcribed at a second program point.

Both branches, with the constructor and the class module, are generated and verified in
`test/counter_class/`.

**R4.12 (constructor).** `new C(args)` emits a function that allocates, establishes the
invariant, and returns the object:

```
fn ctor_C (…args…)
  requires pure ⟦P⟧
  returns  x : class_C
  ensures  exists* m. class_C__inv x m ** pure ⟦Q⟧
```

The postcondition **constrains the initial model** through the constructor's `[Ensures]`,
in the same existential form as R4.10. `ensures class_C__inv x m` alone — for some
unconstrained `m` — would say the object is well formed without saying what it holds, which
is R3.10's weak-specification failure relocated to the constructor. A constructor with no
`[Ensures]` is therefore a warning (`PALCS0903`): it is legal, and almost never what was
meant.

The rule is not the constructor's, it is *the class-typed return's* — R9.15d — and the
constructor is its first instance. Any method whose return type is a class owns the
returned object in its postcondition, existentially at its model; the constructor differs
only in binding that model to `this`, which is what lets its `[Ensures]` read like every
other method's.

Freshness is free and needs no emitter work: the frame rule gives every caller
`frame ** class_C__inv x m₀`, so a newly constructed object is automatically separate from
everything that already existed.

**R4.12c (chaining).** `C(…) : this(args)` **is** the call `ctor_C_sig(args)`, and the
chaining constructor's whole body is that call:

```
fn func_Box__ctor_unit ()
  requires emp
  returns  x : class_Box
  ensures  exists* m. class_Box__inv x m ** pure ⟦Q⟧
{
  let t0 = func_Box__ctor_int 0l;
  t0
}
```

There is no new rule here, which is the point: R9.15d already says a method returning a
class owns the returned object at an existential model, and a chaining constructor is such
a method whose body is one call. The chaining constructor's own `[Ensures]` is then
discharged from the chained one's, by Pulse, from the contract alone — so a convenience
overload is checked against the general constructor rather than re-proved.

**A body after the call (R27.45).** `C(…) : this(args) { S }` runs the chained
constructor, then `S` over the object it returned, opened as an instance method's receiver
is (R4.10), and closes it at the end like R22.9's open constructor. All `S` knows of the
object at the start is the chained constructor's postcondition, which is C#'s own order of
evaluation: the chained constructor finishes before the body starts.

`: base(...)` is a separate question and waits on a base class that has fields at all
(§8.6, and R9.2 is why).

**R4.12d (field initialisers).** `private int x = 7;` **is** the assignment `this.x = 7;`
placed at the head of the constructor, ahead of its body. That is where C# runs it, so
R4.12 continues to read one list of assignments and needs no case of its own; a field the
initialiser sets and the body sets again is set twice in that order, and the second wins,
because assignments are sequential and nothing here made them otherwise.

It runs in exactly the constructors C# runs it in — those that do **not** chain with
`: this(...)`. That is not a choice either: a chaining constructor's initialisers ran in
the constructor it chained to, and running them again would build a representation twice.
R4.12c's shape already says so, since a chaining constructor's body is a call and has no
allocation in it at all.

**R4.12b (a constructor consumes its object parameters).** A constructor body may only
initialise fields (R4.12), so an object it is *given* has nowhere to go except into the
representation it is building. Ownership therefore moves, whether or not the author wrote
`[Consumes]`, and the rule is read off the shape of a constructor rather than off an
annotation. Keeping the argument's invariant in the postcondition would ask the caller to
own the same object twice. R27.45 narrows this to a body that may *store* the reference:
one that uses it other than as the receiver of a field read or a method call, or in a null
test. A copy constructor that only reads from the object it is given hands it back.

**R4.9c/R4.12b on the calling side.** The two ends have to agree, or the resource is owned
twice or not at all, so consumption is one predicate over `(method, parameter)` consulted by
both. At a call site, an argument at a consumed position stops being owned: it is not folded
back by R4.14, and it may not be handed to anything else. C# would leave the name usable —
the reference is still there — so a later use is **PALCS0550**, reported against the second
use rather than left to surface as an unprovable resource in generated Pulse.

**R4.14 (the garbage collector).** An object whose reference does not leave the method is
**dropped at every exit**:

```
with m. assert (Class_C.class_C__inv var_x m);
drop_ (Class_C.class_C__inv var_x m);
```

This is where the CLR's collector enters the translation. F15 says the resource *may* be
discarded; F18 says the discard must nonetheless be *written*, and that writing it needs a
name for a model the emitter never chose — hence the `with`. A returned object is exempt:
its invariant is in the postcondition.

A returned object also keeps the binder its callee produced it under. Pulse matches
resources syntactically, so `let var_c = t0` leaves the context holding `inv t0 _` while
the postcondition asks for `inv var_c _`, and the frame rule cannot bridge the two even
though the equality is trivially true (`Error 228`). The emitter therefore emits a call
that initialises an object local *into that local's binder* rather than into a temporary
the local then aliases.

**R4.14b (an object local that is an alias).** `C x = y;` where `y` already names an object
allocates nothing. It binds a second C# name to one object, so the translation is to bind a
second *slot* to one Pulse binder: `x` and `y` denote the same term, and nothing at all is
emitted for the declaration.

That is forced from both sides. R4.14 would otherwise discard `x`'s invariant at the end of
the method — but `x` owns nothing, the invariant belongs to `y`, and the discard would take
the resource the method has to hand back. And emitting `let var_x = var_y;` would not help:
the context would hold `inv var_y _` while every later mention asked for `inv var_x _`,
which is the same syntactic gap R4.14's last paragraph closes for a returned object, in the
other direction.

Sharing the slot also makes R5.13 do the right thing without knowing about aliases at all.
`Pal.Share(x)` becomes the lemma applied to `var_y`, because that is the object there is —
and the case where an alias is what makes the split worth writing is exactly the case
`test/frac_alias`'s variant is built around.

**R4.14a (where an object may be allocated).** R4.14's discard lands at the end of the
block that declares the object — which is where C# says the name goes out of scope, and
not merely at the end of the method: an object allocated in one arm of an `if` must not be
discarded in the other, where its binder does not exist.

F19 then bounds where the declaration may appear. The discard has to be checked against
the enclosing block's postcondition, and only a block that ends at the method's exit has
one. So an object local may be declared in the method's own block, or in a branch that
returns; in a block that *closes* around it — a statement-position `if`, a loop body — it
is **PALCS0001**. The message says where to move it.

**R4.15 (statements inside the window).** R4.10's bracket is open across the whole body,
so every statement in an instance method runs where the object's invariant does *not* hold
and the receiver is a representation rather than an object. Two rules follow from that, and
both live in §5 because they are rules about statements: R5.11a for a ghost statement and
**R5.12** for a loop.

**R4.13 (rejections).** M2 is the single-class encoding: a `sealed` class with no base
list, whose per-class `class_C__inv` cannot express behavioural subtyping. `virtual`,
`abstract` and `override` are not rejected — §9 encodes them, and R9.21 admits an open
concrete class by desugaring — but interface implementations still are (**PALCS0546**).
A **static mutable field**
is **PALCS0522** — it is unowned global mutable state, which no per-object invariant
covers. A `[Spec]` member that reads a field directly is **PALCS0523** (R3.9c), and a class
with no `[Model]` member is **PALCS0524**: without one there is no model, and without a
model every method spec collapses to memory safety.

---

## 5. Statements

**R5.1 (sequence).** `s₁ s₂ … sₙ` ⟶ `⟦s₁⟧; ⟦s₂⟧; …; ⟦sₙ⟧`. **Order is preserved.** The
emitter never reorders, merges, or elides a statement.

**R5.2 (local declaration).** `T x = e;` ⟶ `let mut var_x : ⟦T⟧ = ⟦e⟧;`. Every C# local is
a Pulse `ref` cell; a read of `x` is `!var_x` (R6.1). Locals are *not* promoted to
immutable `let` bindings merely because they are never reassigned — that would be an
optimisation, and optimisations are how translators start fitting examples. R5.2a is the
one exception, and it is about what a proof can know, not about speed.

**R5.2a (a non-arithmetic local that is never written).** A local of type `bool`, `string`,
an `option`, a `[SpecType]` or an exception, declared with an initialiser and never the
target of an assignment, increment or `ref`/`out` argument anywhere in its scope, is
`let var_x = ⟦e⟧;` — a value, not a cell. A cell's contents are generalised at every join
of a stateful `if` (Pulse's join quantifies them afresh), so a fact about what `x` was
initialised to, such as `bool hasCurrency = r != null && …;`, is lost the first time
control merges after a branch that raised. A value cannot be generalised, so the fact
survives. Arithmetic locals keep their cell: there the initialiser reaching the solver as
an inlined term rather than as a name is what destabilises proofs (`examples/adler32`).

**R5.3 (assignment).** `x = e;` ⟶ `var_x := ⟦e⟧;`. `a[i] = e;` ⟶ `array_write var_a (Idx ⟦i⟧) ⟦e⟧`
after A-normalisation (R6.2). Compound assignment `x op= e` is normalised to `x = x op e`
and `x++` to `x = x + 1` in the Normalize pass, which is a C#→C# rewrite.

**R5.3a (the L-value is evaluated once).** That rewrite names the L-value twice — three
times for the expression form `x++`, which also snapshots it — and C# names it once and
evaluates it once (ECMA-334 §12.18.3, §12.21). For an L-value with no effects the
difference is invisible. For `a[Bump(ref cursor)]++` it is not: a translation that spliced
the lowered L-value into each position would call `Bump` twice, advance the cursor by two,
and increment an element the C# never touches — and would then *prove* the cursor advances
by two, which is a theorem about a different program.

So the effectful part of an L-value is evaluated once, into a fresh immutable local, and
every copy of the L-value names that local — the same discipline R5.14 already applies to
a `switch` scrutinee. This is possible for an **index**, which is a value. It is not
possible for the array or the receiver, which are resources: hoisting one is a move, not a
binding. There the expansion is refused (**PALCS0578**) rather than approximated.
`test/step_once` pins the single evaluation; `test/pulse_refusals/cases/StepCountedTwice.cs`
is the false theorem, which must now fail.

**R5.4 (`if`).** `if (c) s₁ else s₂` ⟶ `if (⟦c⟧) { ⟦s₁⟧ } else { ⟦s₂⟧ }`. **Both branches
are always emitted**, even when one is empty.

**R5.5 (`return`).** `return e;` ⟶ `⟦e⟧` in tail position.

**R5.5b (early return).** Pulse has no non-tail `return`, so the Normalize pass rewrites
one away as a **C#→C# transformation**: a statement sequence `s₁ … sₖ rest` in which `sₖ`
is an `if` whose taken branch ends in a `return` becomes

```csharp
s₁ … if (c) { thenBranch } else { elseBranch; rest }
```

so that every `return` is in tail position. The rewrite is driven by the syntactic
predicate "does this branch end in a `return`", is applied uniformly, and preserves the
order and the identity of every statement — it neither duplicates code nor introduces a
flag. `return` inside a loop is *not* restructured; it is rejected with a diagnostic, since
turning it into a flag-driven loop would be the translator inventing control flow.

**R5.6 (`while`).**

```csharp
while (c) { Pal.Invariant(I₁); … Pal.Decreases(m); B }
```

⟶

```
while (⟦c⟧)
invariant ⟦live-set⟧ ** ⟦frame⟧ ** pure (⟦I₁⟧ /\ …)
decreases ⟦m⟧
{ ⟦B⟧ }
```

By F1 and F8 the guard `⟦c⟧` may be a stateful block, so no flag encoding is used. The
`decreases` clause takes **no trailing semicolon** (§1).

A Pulse loop body sees the invariant and nothing else. The emitter therefore does **not**
propagate the enclosing `requires` into the loop; a fact the body needs is the annotation
author's responsibility to restate as an invariant. Inventing invariants is exactly the
"emitter invents proof steps" failure §0 rule 3 forbids.

**R5.7 (`for` → `while`).** `for (init; cond; step) { body }` ⟶
`{ init; while (cond) { body; step } }` as a **C#→C# rewrite** in the Normalize pass. The
emitter only ever sees `while`.

One qualification, for R5.10's sake: C# runs `step` after a `continue` but not after a
`break`, and appending `step` to `body` loses that distinction. So when the body contains
an escape the step is *not* appended; it is carried in a separate slot on the `while` and
emitted by R5.10 under the break flag alone. When the body contains no escape the two are
indistinguishable and the step is appended, as above.

**R5.8 (`live` inference).** The `invariant` includes `pts_to` for every local the loop body
reads or writes, computed from the body's free variables. This is an improvement over PAL,
which requires an explicit `_invariant(_live(x))` per local. It is a syntactic function of
the body, not a search: it does not depend on what the loop is *for*. `Pal.Live(x)` adds a
resource the inference cannot see.

**R5.8b (frame for unassigned locals).** A local that the loop body **never assigns** keeps
its value across the loop, so the emitter binds that value *outside* the loop
(`with v. assert (pts_to var_x v);`) and writes `pts_to var_x v` in the invariant, rather
than existentially quantifying it. Whether a local is assigned is a syntactic property of
the body — it does not depend on what the loop is for — so this is a rule, not an
inference.

Without it, nothing connects the local's value before and after the loop. The
insertion-sort probe found this the hard way: the outer loop's step `i = i + 1` could not
be shown to decrease the measure, because the *inner* loop had existentially rebound `i`
even though it never touches it.

For an **object**, "assigned" is R4.11c's question, not `Assigned`'s: a loop that only
*reads* an object through a read-only method holds its model fixed. The same shape, one
level up, as the defect R4.11c describes — a loop that dispatches a reader on a shape it
was handed must still be able to return that shape to its caller with the model the caller
named.

**R5.8c (an invariant that owns).** A `Pal.Invariant` clause is sorted by exactly the test
R12.2 applies to a contract: a clause of type `SlProp` is a **resource** and joins the
`pts_to`s; anything else is a proposition and joins the single `pure`. There is no third
case and no analysis of what the clause says.

The rule is small and it is what makes a *cursor* expressible. R5.8's inference computes the
ownership of the loop's **locals**; it has nothing to say about the part of a heap data
structure the loop is standing in the middle of, because that is not a function of the
body's free variables — it is a function of the loop counter. Without R5.8c an invariant
could state facts about values only, and every iterative traversal would stay out of reach
whatever the library offered.

**R5.8d (the last statement of a loop body is in tail position).** Exactly as the last
statement of a method body is. A `let mut` in Pulse needs a postcondition at the end of its
scope, and it has one only where that scope ends in a construct carrying an annotation; an
`if` terminated by `()` is not such a construct, so a `let mut` inside either of its
branches is rejected with *"Allocating a mutable local variable expects an annotated
post-condition"*. Since §12 asks every cursor loop to read fields inside the non-null branch
of a test, and a field read binds a cell, the same body was typable as a method's tail and
untypable as a loop's.

The rule recurses through blocks and two-armed `if`s, so a nest of them is a nest of tails.
Two exclusions, both principled rather than incidental:

* a null test that opens a §10 window is **not** a tail, because the window's closing lemma
  is emitted on the non-tail path — moving it would be a change to R10.7, not to where a
  block ends;
* a loop with a `for` step, a `break` flag or a `continue` flag is **not** a tail, because
  in each of those the body is followed by something.

**R5.9 (`decreases` obligation).** By F2 every emitted `while` **must** carry `decreases`.
The measure is obtained, in order:
1. an explicit `Pal.Decreases(m)` in the loop body ⟶ `⟦m⟧`;
2. otherwise, for a loop whose Normalize-pass origin is a counted `for` with a monotone
   integer step — guard `i < h` with step `i = i + k`, `k > 0` — the measure
   **`pow2 31 - Int32.v !var_i`** (and `Int32.v !var_i + pow2 31` for a decreasing
   counter). Note it does **not** mention the loop's upper bound `h`. That is deliberate
   and was forced by the probe: `h` is very often `a.Length`, which is not available as a
   pure expression at the point `decreases` is checked. Since the counter has type `int`
   it is bounded by its own type, and the type's bound is a measure — one that is always
   available, always non-negative, and never requires looking at what the loop is
   counting over. This is a *syntactic* pattern on the loop's own shape, and it satisfies
   F3's requirement that the measure dereference locals rather than invariant
   existentials;
3. otherwise the translation **fails with a diagnostic** demanding `Pal.Decreases`.

Case 3 is deliberate: guessing a measure would be the emitter inventing a proof step
(Rule 3).

**R5.10 (`break` and `continue`).** Pulse has neither. Both are translated with *escape
flags*, allocated only for the forms the body actually uses, so a loop with no escape is
emitted exactly as R5.6 describes.

| C# | Pulse |
|---|---|
| a loop whose body contains `break` | `let mut var_brk_n = false;` **before** the loop |
| a loop whose body contains `continue` | `let mut var_cont_n = false;` as the **first statement of the body**, so it is cleared on every iteration |
| `break;` | `var_brk_n := true;` (and `var_cont_n := true;` if that flag exists) |
| `continue;` | `var_cont_n := true;` |
| guard `c` | `⟦c⟧ && not !var_brk_n` |
| invariant | additionally `exists* v. pts_to var_brk_n v` |
| measure `m` | `CA.until_set !var_brk_n (⟦m⟧)`, i.e. `if brk then 0 else ⟦m⟧ + 1` (R27.10) |
| `S₁; S₂` in a loop body, where `S₁` may escape | `⟦S₁⟧; if (not !var_brk_n && not !var_cont_n) { ⟦S₂⟧ } else { () };` |
| the `for` step of R5.7 | emitted after the body, under `not !var_brk_n` only |

Four points are worth stating because each is forced, not chosen:

* **The user's guard comes first.** In a short-circuit guard `e₁ && e₂` only `e₁`'s
  dereferences stay visible to the loop body, so appending the flag rather than prepending
  it is what keeps R5.6 loops unchanged.
* **The measure needs the flag.** The iteration that breaks need not decrease the user's
  measure — it exits instead. `until_set` is `m + 1` while the flag is clear and `0` once
  it is set, so the breaking iteration decreases it whatever state it leaves behind
  (R27.10 says why that matters). It stays *linear*, which matters: multiplication in a
  measure puts Z3 into nonlinear mode and destabilises unrelated obligations in the same
  definition. And it stays inside F9, which forbids a dereference in a *branch* of an
  `if` in a measure: the flag and the measure are a function's arguments, not an `if`'s.
* **`var_cont_n` needs no invariant** because it is allocated inside the body and so does
  not cross the loop's boundary.
* **The guard is a syntactic test.** "May escape" is a walk over the statement that stops
  at a nested loop, whose own `break` and `continue` bind to that loop. It never looks at
  what the loop computes.

**R5.11 (ghost statements).** `Pal.Assert(p)` ⟶ `assert (⟦p⟧)`. A call to a `[Lemma]`
method ⟶ the corresponding ghost call. `Pal.GhostStmt("…")` ⟶ the string verbatim, after
antiquotation expansion.

A ghost statement is a proposition about values, and the context holds resources, so the
values have to be named first. The emitter emits `with v₁ … vₙ. assert (r₁ ** … ** rₙ);`
over everything the method owns, and binds each `vᵢ` in the scope the proposition is
elaborated in — F18's idiom, used to *read* rather than to discard.

**R5.11a (a ghost statement inside R4.10's window).** In an instance method the receiver is
not among those resources: R4.15 says the invariant is unfolded, so `class_C__inv this m`
is precisely what the context does not hold and asserting it would fail. R5.12's
representation is named instead — the same `B.pts_to`, the same one `A.pts_to` per array
field, the same `this.f` scope bindings — which is also what lets the proposition mention a
field:

```csharp
Pal.Assert(n <= items.Length);
```
⟶
```
with vrep vcontents_items. assert (B.pts_to var_this vrep **
                                   A.pts_to vrep.Class_Bag.fld_items vcontents_items);
assert (pure ((I32.v vrep.Class_Bag.fld_n) <= (Seq.length vcontents_items)));
```

**R5.12 (a loop inside R4.10's window).** A loop in an instance method sits where the
invariant is unfolded, so what it carries is the **representation**, not the object:

| carried | for |
|---|---|
| `B.pts_to var_this r` | the record cell R3.6 gave the class |
| `A.pts_to r.Class_C.fld_f c_f` | each array field `f`, whose contents R3.10a makes part of the model |
| `Class_D.class_D__inv r.Class_C.fld_g model_g` | each object field `g`, still **folded**, so the body may call its methods (R3.10b, F20) |

Each field is bound in the invariant's scope under the key `this.f`, so that a user writing
`Pal.Invariant(n <= items.Length)` inside the method means the representation's `n` and the
representation's contents — the same reading R3.9b gives a class-level `[Invariant]`, and
for the same reason. A scalar field denotes its projection out of `r`; an array field
denotes its contents sequence.

*Which halves are existential* is decided by what the body writes, and the distinction is
not an optimisation:

* A **field assignment** replaces the whole record (R3.6), so it unsettles `r` and, with
  it, every array reference projected out of `r`.
* An **element write** — or handing an owned array to a callee, which may write it —
  unsettles only that array's contents. The record survives, because a record update is
  definitionally equal to the original in every field it does not mention.
* A **call on a sub-object** unsettles only that sub-object's model, and only if the callee
  is not read-only. This is the one case in which a field survives being handed to a
  callee, and it needs a distinction `MutatesReceiver` alone cannot draw — a read-only
  instance call and a static call both leave it false — so the IR records whether a call's
  first argument is a receiver at all.
* Anything the loop leaves alone is **named before the loop** with R5.8b's `with … assert`
  rather than quantified inside it. For the receiver that is essential rather than
  convenient: a read-only method re-folds its invariant at the model it was *handed*
  (R4.11a), and an existentially quantified record could not possibly abstract to it.

Two pure conjuncts are the emitter's, and only two, because both come from C#'s array type
rather than from anything the user wrote:

* `Seq.length c_f <= 2147483647` — R3.10a's bound, restated because an existential remembers
  nothing.
* `Seq.length c_f == Seq.length c⁰_f` where the contents are existential but the record is
  not — no C# operation changes the length of an array it has been handed, so a loop that
  writes only elements leaves the length where it was. `c⁰_f` is named before the loop, for
  the same reason and by the same mechanism as the fixed binders above.

What is **not** carried is the class's own `[Invariant]` clauses. They may be transiently
false — that is what the window is for — so a loop that needs `n <= items.Length` says so,
in a `Pal.Invariant` of its own. That is R5.8's rule unchanged: the resources are the
emitter's, the propositions are the user's.

*Interaction with F3.* A `decreases` measure may name a field only where the loop leaves
that field alone, because only then does the field have a binder from *before* the loop.
Where the loop writes it, the binding is simply absent from the measure's scope and naming
it is refused — which is F3's rule (a measure may not mention the invariant's
existentials) arriving as a consequence rather than as a special case.

`test/bag_class` is the acceptance test: `Fill` writes elements (contents existential,
record fixed, length carried) and `Max` writes nothing (everything fixed, so R4.11a's
`preserves` re-fold goes through). `BagVariant.cs` writes both loops as `for` loops and
gets, modulo names, the same Pulse.

**R5.13 (splitting and recombining a permission).** `Pal.Share(x)` and `Pal.Gather(x)` are
ghost statements, `[Conditional]` like every other, and they translate by what `x` is:

| `x` | `Pal.Share(x)` | `Pal.Gather(x)` |
|---|---|---|
| an object of class `C` | `Class_C.class_C__inv_share ⟦x⟧;` | `Class_C.class_C__inv_gather ⟦x⟧;` |
| an array | `A.share ⟦x⟧;` | `A.gather ⟦x⟧;` |

They exist because **Pulse does not split a permission on its own** (F25). Passing one
object to two observed parameters fails with `Cannot prove: class_C__inv s _` against a
context holding exactly that resource, and the same is true of an array — so R4.9's
standing claim that "the same array may be passed to two parameters at once" was, until
this rule, not actually reachable. `test/pulse_facts` now pins both halves.

The design question this rule answers is *who* writes the split, and there were two
candidates.

*The emitter could insert it*, at a call site passing the same argument twice. That is
§0 rule 3's forbidden move in its purest form: a proof step invented by the translator in
response to the shape of one call. It also could not work — the emitter would have to
recognise the aliasing to know when to split, which is exactly the recognition R3.13 has
just finished establishing that a frontend cannot do. Two objects reached through fields,
or aliased three statements earlier, need the same split and present no syntactic sign of
it.

*Or the user writes it*, which is the choice, and it is the ordinary one: a split is a
proof step, proof steps come from the user's annotations, and `Pal.Share` sits beside
`Pal.Assert` and a `[Lemma]` call as one more of them. It costs a line, and the line says
something true about the program that was not otherwise written down — that from here on
this object is being read, not owned.

Four consequences.

* **`Gather` is `Share`'s exact inverse, so the pair round-trips with nothing in between.**
  This is what R3.10d's third lemma buys (F24): without it every `Gather` would be followed
  by a `rewrite` about `p /. 2.0R +. p /. 2.0R`, which is a fact about the encoding and not
  about the program.
* **`Gather` proves the two views agreed** (F23), so nothing needs to be re-established
  after one. A caller that shared, observed through both halves, and gathered knows the
  model is the one it started with.
* **Sharing more than twice is sharing twice, twice.** `Share` halves; three observers take
  two shares and two gathers. Nothing bounds the depth.
* **`Pal.Share(this)` inside an instance method is Pulse's to refuse.** R4.15 says the
  receiver's invariant is unfolded there, so the lemma's precondition is precisely what the
  context does not hold. The frontend says nothing about it — §0 rule 3, other direction.

**R5.14 (`switch` becomes an if/else chain).** Like R5.7's `for`, a `switch` is lowered
intact and desugared by Normalize, so the rewrite is one rule applied uniformly rather
than a shape the frontend recognises:

```csharp
switch (e) {                       {
  case k1:                             var t = e;             // once
  case k2: S1; break;          ==>     if (t == k1 || t == k2) { S1 }
  case k3: S2; break;                  else if (t == k3)      { S2 }
  default: S3; break;                  else                   { S3 }
}                                  }
```

Three things in that picture are load-bearing.

*The scrutinee is bound, always.* C# evaluates the governing expression exactly once, and
an if/else chain tests it up to *n* times. For `switch (a[i++])` the difference is
observable, so the binding is not an optimisation to be applied when it happens to matter
— it is what makes the rewrite correct. It is an immutable binding (the `Immutable` flag
R13.3 introduced), because it is written once and read many times, and because a cell
declared here would become a resource in every enclosing block.

*The `default` section moves to the end.* C# lets it be written anywhere among the
sections, and it always means "none of the others". Reordering is sound precisely because
C# requires the case labels to be *distinct constants*: no two arms of the chain can both
be taken, so the order among them carries no information. A `switch` with no `default` has
no final `else`, which is the same fallthrough-to-nothing C# gives it.

*A section's trailing `break` is dropped, and any other `break` is refused.* This is the
one place a naive desugaring is quietly wrong. Inside a `switch`, `break` means "leave the
switch"; inside a loop it means "leave the loop"; and a `switch` inside a loop has both
meanings in scope, distinguished only by which construct encloses the statement. The final
`break` of a section is the section terminator and vanishes with the section. But

```csharp
while (…) { switch (k) { case 1: if (c) break; S; break; …
```

has a `break` whose meaning *changes* under the rewrite: it left the `switch` before and
would leave the `while` after. There is no if/else chain that expresses it — the chain has
no construct to break out of — so it is rejected (PALCS0577) rather than mistranslated.
`continue` needs no such care: it targets the enclosing loop both before and after.

The rest is refusal, and each refusal is a construct with no meaning in the chain rather
than one that is merely unimplemented. Pattern labels and `when` guards (`case int x:`,
`case > 0:`) are rejected: they bind and test rather than compare, and R5.14 is a rule
about equality against constants. `goto case` and `goto default` are rejected as the
arbitrary control flow they are. A section that does not end in `break`, `return` or
`continue` cannot occur — C# itself forbids the fallthrough — and stacked labels
(`case k1: case k2:`) are one section with two labels in Roslyn's tree already, which is
why they need no rule of their own beyond the disjunction above.

What this rule does *not* do is give the solver a case analysis it did not have.
`if (t == k1) … else if (t == k2) …` is exactly the term structure a hand-written chain
would produce, so a proof about a `switch` costs what the same proof about the chain
costs. That is the intended outcome: `switch` is a notation, and R5.14 says it is only a
notation.

The variant test (§7.2) earned its keep twice here, and neither finding was about
`switch`. Both were about *where* the rewrite sits among the rules that were already
there.

* **A rewrite must run before anything that analyses what it produces (F57).** R5.7 asks
  whether a loop body escapes, to decide whether the `for` step belongs in the body or in
  its own slot. Asked before R5.14 has run, it does not see a `continue` still inside a
  `switch`, appends the step to the body, and the step is then skipped on exactly the
  iterations that continue — so the counter stalls and *termination* fails. The symptom is
  a failed measure, four rules away from the cause.
* **A rewrite that introduces a binding must splice, not nest (F58).** The scrutinee
  binding wrapped the chain in a block, and R5.5b absorbs a tail only into a chain that is
  a statement of the *same* block. So a `switch` whose sections `return` was rejected with
  every piece of R5.14 correct. Fixing it generalised R5.5b, which previously absorbed
  only into an `if` with no `else` and now absorbs into a chain of guards — a shape a
  hand-written program can have too, and which it had been silently refusing.

Neither fix is a special case for `switch`: one is an ordering constraint between two
existing passes, the other a rule that was too narrow. That is §0 rule 3 working as
intended — the cost of a new construct is paid in the general rules or not at all.

### Why not a Pulse `match`?

Because a C# `switch` looks like one, and structure-preserving is what §0 asks for, this
is the first question to ask about R5.14 — so it is worth saying what the answer rests on,
which has changed once already.

When R5.14 was written the answer was that Pulse could not do it: `0l` in pattern position
was read as a `Prims.int` and rejected against an `Int32.t` scrutinee. A chain was not
chosen over `match`, it was the only target there was. FStarLang/FStar#4374 (merged
2026-08-02) fixed that, and `test/pulse_facts/MatchFacts.fst` now verifies a Pulse `match`
on `Int32.t` and `UInt8.t` literals. So the question is live, and the chain has to be
argued for rather than assumed.

**It loses on one point, and that point is decisive: Pulse has no or-patterns (F60).**
A C# section carries a *set* of labels —

```csharp
case 0:
case 1:
    S;
    break;
```

is one section with two labels, not two sections. `match` can only express it by
duplicating `S` once per label, and nothing bounds the number of labels. `S` is the user's
code: their `Pal.Assert`s, their lemma calls, their loops. Duplicating it duplicates proof
obligations they wrote once, and reports each failure twice against the same C# span.
`t == k1 || t == k2` is one branch, of any width, at no cost. (F\* itself has or-patterns,
so this is a property of Pulse's `match` and may not be permanent.)

**And it wins nothing to set against that.** The intuition that a `match` gives the solver
a case analysis a chain does not is wrong here: a machine integer is not an inductive type,
so an arm's hypothesis is exactly the equality `I32.v k == 0` that the `if` branch already
supplies (F59). `MatchFacts.fst` discharges the same assertion both ways to make the point
checkable rather than plausible. The other candidate advantages are smaller than they
look. `match` would evaluate the scrutinee once natively, saving the binding — but the
binding is one immutable `let`, and it is what makes the *rewrite* obviously correct.
Pulse would check exhaustiveness — but C# has already done that, and a `switch` with no
`default` is not an error in C# and must not become one here. `default` would still need
hoisting, because match arms are ordered too.

So: the chain, until Pulse has or-patterns. That is the condition to re-open this on, and
it is a fact about Pulse rather than a preference — which is the point of writing it down
here instead of leaving it as a decision nobody recorded.

### What C# rules out, and what PAL has to do about it

The rewrite above is only as simple as it is because **C# forbids implicit fallthrough**
(CS0163). Every section is entered exactly one way — by matching one of its own labels —
so the sections are disjoint and an if/else chain, whose arms are disjoint too, is a
faithful target.

PAL translates C, which has no such rule, and the difference is visible in the shape of
its desugaring. `pal/cpp/impl.cpp` reads:

```
// Desugar: switch (scrutinee) { case v1: s1; case v2: s2; default: sd }
//      --> let scrut = scrutinee;
//          bool hit = false; bool brk = false;
//          if (!brk && (hit || scrut == v1)) { hit = true; s1 }
//          if (!brk && (hit || scrut == v2)) { hit = true; s2 }
//          if (!brk) { sd }
// break inside case bodies sets brk = true.
```

Three of those pieces exist for fallthrough. `hit` is a flag that makes a section run
because an *earlier* one did; the arms are a sequence of independent `if`s rather than a
chain, because more than one may run; and `brk` is a real variable rather than a
structural exit, because `break` has to stop that sequence part-way. pal-csharp needs none
of it: the scrutinee binding is shared, and everything else falls away. That is a language
difference doing real work, not a difference in ambition — and it is worth naming, because
"how does PAL do it?" would otherwise import machinery for a case that cannot arise.

`goto case` and `goto default` are the exception C# leaves open, and they ask for precisely
what the chain cannot express: entry into one arm from inside another. They are refused,
with a message naming the two honest rewrites — stack the labels when the other section
should run *instead*, factor out a method when it should run *as well*
(`test/diagnostics/cases/GotoCaseFallthrough.cs`). Approximating them would mean adopting
PAL's `hit` flag for the one construct C# already discourages.

One further thing PAL needs and pal-csharp does not: a **join contract**. Its
`switch_stmt.c` carries `switch (x) _ensures(_live(x) && _live(result))` — an annotation
at the point where the arms rejoin, because the desugaring's arms are a *sequence* and
the resources have to be re-established between them. A chain has a structural join, which
Pulse's `if` already types, so there is nothing for the user to write.

---

## 6. Expressions

**R6.1 (variables).** A read of local or rebound parameter `x` ⟶ `!var_x`. A read of a
non-rebound by-value parameter `p` ⟶ `var_p`.

**R6.2 (A-normalisation).** C# expressions may nest effectful subexpressions; Pulse
statements are atomic. Every effectful subexpression (array read, method call) is therefore
lifted into a `let` binding, **in C#'s guaranteed left-to-right evaluation order**:

```csharp
a[j + 1] = a[j];
```
⟶
```
let t0 = array_read var_a (Idx (!var_j));
array_write var_a (Idx (!var_j + 1l)) t0;
```

This is a single uniform rule, not a peephole. Pure subexpressions are not lifted.

**R6.3 (short-circuit operators).** By F1:

* `e₁ && e₂` ⟶ `let t = ⟦e₁⟧; if (t) { ⟦e₂⟧ } else { false }`
* `e₁ || e₂` ⟶ `let t = ⟦e₁⟧; if (t) { true } else { ⟦e₂⟧ }`
* `c ? e₁ : e₂` ⟶ `if (⟦c⟧) { ⟦e₁⟧ } else { ⟦e₂⟧ }`

When `e₂` is pure, this degenerates to the plain Pulse operator. The rule is stated once
and applies identically in a loop guard, an `if` condition, and an assignment RHS —
which is exactly what makes insertion sort's `j >= 0 && a[j] > key` unremarkable.

**R6.4 (arithmetic and proof obligations).** `e₁ op e₂` ⟶ the corresponding
`Pulse.Lib.CSharp.Int32` operation, which carries the obligation. C# semantics differ from
C's, so the scheme fixes:

| Construct | C# runtime behaviour | Obligation |
|---|---|---|
| `x + y`, `x * y`, … | wraps (`unchecked`, default) | **no overflow** |
| `a[i]` | throws `IndexOutOfRangeException` | `0 <= i < a.Length` |
| `x / y`, `x % y` | throws `DivideByZeroException` | `y != 0` |
| `o.f` | throws `NullReferenceException` | `o != null` |

A verified program therefore **throws no exception**; `try`/`catch`/`throw` are rejected. The
no-overflow choice matches PAL and is revisited if it proves onerous; `[Unchecked]` would
opt into a wrapping model.

**R6.4a (what `/` and `%` mean in a specification).** C#'s `/` and `%` round toward zero;
F*'s `Prims.op_Division` and `op_Modulus` round toward minus infinity. On a negative
operand the two disagree — `-7 / 2` is `-3` in C# and `-4` in F*, and `-7 % 2` is `-1` and
`1` — so the choice is not a matter of taste. A specification is read by someone reading
C#, and where it quotes a C# expression it has to *mean* the C#; otherwise the reader and
the prover agree on the string and disagree on the claim, and they disagree only about a
sign the reader was not thinking about.

In spec position, therefore, `e₁ / e₂` ⟶ `CA.cdiv ⟦e₁⟧ ⟦e₂⟧` and `e₁ % e₂` ⟶
`CA.crem ⟦e₁⟧ ⟦e₂⟧` **when both operands are machine integers and at least one is
signed** — the only configuration in which the divergence is reachable. `CA.cdiv` is
`FStar.Int.( /- )`, the truncating division, and `CA.crem a b` is
`a - (cdiv a b) * b`. Both live in `Pulse.Lib.CSharp.Arith` (§0 rule 3: a fact about
integers is filed under arithmetic, not under the first client that wanted it). Otherwise
the operators are F*'s own:

- over a spec-only numeric (`SpecInt`, `SpecNat`) there is no C# operator to disagree
  with — the expression is mathematics, and `/` is the floor division it looks like;
- over unsigned machine integers both operands are non-negative, where the two roundings
  coincide exactly, so F*'s operators already *are* C#'s.

`CA.cdiv_nonneg` and `CA.crem_nonneg` are `SMTPat` lemmas identifying the two on
non-negative operands, which is where most specifications live; `CA.cdiv_crem` gives the
division identity. In code position nothing changes: `I32.div` was always
`FStar.Int.( /- )`, so the *program* side was faithful throughout. It was
the specification side that read C# syntax with F*'s meaning, and a method computing
floor division could carry `[Ensures("Result == x / 2")]` and be believed
(`test/pulse_refusals/cases/FloorDivContract.cs`; `test/spec_division` pins both sides).

**R6.4b (bitwise, shift and complement operators in a specification).** R6.4a's question,
asked of the rest of the operator table. `&`, `|`, `^` and unary `~` over machine integers
have an exact image: `FStar.Int32.logand` is specified as `v c == Int.logand (v a) (v b)`
and `lognot` likewise, so in spec position `e₁ & e₂` ⟶ `FStar.Int.logand #w ⟦e₁⟧ ⟦e₂⟧` and
`~e` ⟶ `FStar.Int.lognot #w ⟦e⟧` — `FStar.UInt` where the operands are unsigned, `w` their
common width — and a postcondition that quotes the code is discharged by the code. Both
operands must be machine integers of the same kind: the operation is defined on `int_t n`,
and `I32.v x` is exactly that.

Everything else in the family is **refused** (`PALCS0001`). A bitwise operator over a
spec-only numeric is bit manipulation of a number with no width. A shift is C#'s *masked*
shift — §12.11 takes the count mod 32 or 64, so `x << 33` is `x << 1` — and F*'s
`shift_left` carries a precondition on the count instead of masking, so there is no F*
term that means C#'s `<<` until that masking is written down. §0 rule 3: refuse what
cannot be translated rather than translate it into something else.

The rule exists because **both** operator tables ended in a catch-all. The binary table's
returned `+`, so every operator it did not recognise — `&`, `|`, `^`, `<<`, `>>` — was
emitted as addition, and `[Ensures("Result == (x & 0)")]` reached F* as `Result == x + 0`,
which a method returning `x` proves. Run as C#, it prints `7` where the certificate said
`0`. The unary table's was quieter and worse: it returned the operand *with the operator
dropped*, so `~e` meant `e`, and `[Ensures("Result == ~(x + 1)")]` — which in C# claims
`-(x + 2)` — reached F* as `Result == x + 1`.

That is R6.4a's disease in a much more virulent form: `/` and F*'s `/` at least agree on
most inputs, while `&` and `+` agree on almost none. A default arm is a wrong answer given
silently, and a specification is the one place a wrong answer cannot be caught downstream
— the prover checks the translation, not the C#. Hence §0 rule 3a's shape: no catch-all,
and an operator with no rule is refused by name.

The unary case carries a lesson about probing, too. `~x` *alone* produced an F* type error
rather than a false proof, because the dropped operand was still an `I32.t` where a
mathematical `int` was wanted — so the obvious probe made the hole look like a translator
limitation. Only with an operand that is already mathematical (`~(x + 1)`) does the
emission typecheck and the false theorem go through. A probe that stops at the first error
message can miss an unsoundness sitting one expression away
(`test/pulse_refusals/cases/BitAndContract.cs`, `BitNotContract.cs`,
`test/diagnostics/cases/ShiftInSpec.cs`; `test/spec_bitwise` pins the accepted side).

**Known incompleteness.** No SMT patterns are supplied for these operators, so a
specification needing a *fact* about them — that `x | 0 == x`, or that `x & 255 < 256` —
must supply it, with a `[Lemma]` or `Pal.Assert`. Global patterns on `logand` were
deliberately not added: `Pulse.Lib.CSharp.Casts` already carries patterns on the *idioms*
`logand` appears in (F53), and `examples/adler32` depends on them, so a general pattern is
a proof-stability risk taken for no program that currently needs it. §0 rule 3's usual
route applies when one does — a general lemma in `Pulse.Lib.CSharp.Arith`.


**R6.5 (array access).** `a[i]` ⟶ `array_read var_a (Idx ⟦i⟧)` in code, and
`Seq.index s (Int32.v ⟦i⟧)` in spec position, where `s` is the array's contents
existential. `a.Length` ⟶ R3.3.

**R6.6 (calls).** `C.M(a₁, …)` ⟶ `func_M ⟦a₁⟧ …` after A-normalisation. `[Spec]` methods are
callable in spec position and emit `Let_M.fst`; `[Lemma]` methods emit ghost calls.

**R6.7 (quantifiers).** `Pal.Forall((T i) => p)` ⟶ `forall (i: ⟦T⟧). ⟦p⟧`; likewise
`Pal.Exists`. `Pal.Implies(a, b)` ⟶ `⟦a⟧ ==> ⟦b⟧`. `Pal.Contents(a)` ⟶ the array's contents
existential, giving specs a `Seq` view.

A quantifier binder is bound *outside* both program states, so it is in scope on both
sides of `Old`: under `forall (int k)`, `Old(a[k])` reads the pre-state array at the
same `k` the postcondition speaks of. Emit therefore extends the pre-state scope with
the binder as well as the current one.

**R6.7b (triggers).** Each quantifier carries an SMT pattern inferred from its body: the
element reads `a[k]`, sequence indexings and `[Spec]` calls whose arguments are binders,
literals, `Old`, `Contents`, lengths, widening conversions or further such terms — never
arithmetic, a comparison or a connective, which are interpreted and illegal in a pattern.
If some terms each mention every binder, the pattern is their disjunction
(`{:pattern t1 \/ t2}`); otherwise one multi-pattern covering every binder is assembled
greedily (`{:pattern (Seq.index s i); (Seq.index s j)}`). A quantifier with no covering set
is emitted without a pattern, as before. A nested quantifier's terms are its own triggers,
not the enclosing one's. F84 is why this is needed.

**R6.7a (sequence vocabulary).** `Pal.Slice(s, i, j)` ⟶ `Seq.slice ⟦s⟧ ⟦i⟧ ⟦j⟧`,
`Pal.SetAt(s, i, v)` ⟶ `Seq.upd`, `Pal.IsPermutation` ⟶ `CS.is_permutation`, and
`Pal.Rotate(s, n)` ⟶ `CS.rotate ⟦s⟧ ⟦n⟧`, the sequence read from `n` and wrapping. Each is
a direct name for an `FStar.Seq` or `Pulse.Lib.CSharp.Seq` function; the emitter adds
nothing. `rotate` is there because it is the abstraction function of any container that
stores its elements at a moving origin, and because its characteristic equation
`⟦Rotate(s, n)[k]⟧ == ⟦s[(n + k) % s.Length]⟧` is a fact about sequences that §0 rule 3
places in the library rather than in the emitter or in one program's annotations.

The *arithmetic* such a container also needs — that offsets less than a period apart have
distinct residues, and that offsets a full period apart share one — is not sequence
vocabulary and is not reached through any `Pal.*` name. It is stated over arbitrary
integers in `Pulse.Lib.CSharp.Arith` and carries SMT patterns on `x % len`, so it applies
wherever a C# `%` appears, to a ring buffer and to a program that has never allocated a
sequence alike.

**R6.8 (projection receivers).** `⟦e.f⟧ = ⟦e⟧′.Struct_S.fld_f`, where `⟦e⟧′` is `⟦e⟧`
parenthesised unless it is already atomic. This is not cosmetic: `!var_s.M.fld` parses in
Pulse as `!(var_s.M.fld)`, a dereference of a projection *out of* a reference, which is
not what C#'s `s.f` on a `ref` parameter means.

**R6.9 (mathematical `[Spec]` results).** R4.6 makes a `[Spec]` method's integer
*parameters* mathematical; its integer *result* is mathematical for the same reason. A
`[Spec] int` emits `: int` with a mathematical body, and an application of it denotes a
mathematical value — so it composes with arithmetic and may be used as an array index. A
`[Spec] bool` emits `: prop`. Nothing else about the two cases differs.

**R6.10 (by-reference arguments).** A `ref`/`out`/`in` argument passes the *cell*, not its
contents:

```csharp
Enqueue(a, ref s, value);
```
⟶
```
let t0 = !var_value;
let t1 = func_Enqueue var_a var_s t0;
```

`var_s` is passed unchanged, so the callee's `requires R.pts_to var_s _` is satisfied by
the caller's ownership of the same cell and the write the callee performs is visible after
the call. Passing anything other than a cell — a temporary, a field, an array element — is
**PALCS0402**; C# does not permit it either.

Two consequences the write-set analysis (R5.4) must respect: a call may write through
*every* by-reference argument and through *every* array argument, so all of those names
must be existentially quantified in an enclosing loop's invariant. Missing one does not
produce an unsound proof — it produces an invariant asserting the call changed nothing,
which simply fails to re-establish.

**R6.11 (array allocation).** `new T[n]` ⟶ `alloc ⟦n⟧ ⟦default(T)⟧`, using
`Pulse.Lib.CSharp.Array.alloc`.

Two things are being read off the CLR rather than off Pulse. The allocation always
succeeds and imposes no deallocation obligation, which is why `Pulse.Lib.Array.alloc` —
a *stack* allocation that must not outlive its frame — is not what is called; and the
result is zero-filled, which is why the initial contents are `Seq.create (v n) 0` and no
initialisation loop is emitted. Both live in the one MODELING AXIOM inside
`Pulse.Lib.CSharp.Array.alloc`, where they can be read, rather than being spread across the
emitter.

An explicit initialiser list, `new[] { 1, 2, 3 }`, is refused. It is an initialisation
loop written as an expression, and unrolling it would put writes into the translation that
no C# statement corresponds to, with nowhere to attach a specification between them.

---

## 7. Worked derivation, and the detectors

### 7.1 A loop, derived rule by rule

The inner loop of insertion sort. Note that nothing below is a choice: each line cites the
rule that produced it.

```csharp
while (j >= 0 && a[j] > key) {      // R5.6
    Pal.Invariant(-1 <= j && j < i);
    a[j + 1] = a[j];
    j--;
}
```

| Step | Rule |
|---|---|
| guard becomes a stateful block `let t = !var_j >= 0l; if (t) { let u = array_read var_a (Idx !var_j); u > !var_key } else { false }` | R6.3 + R6.1 + R6.5 |
| `invariant` gains `pts_to var_j _ ** pts_to var_key _ ** array_pts_to_full var_a _ _` | R5.8 |
| `invariant` gains `pure (-1 <= Int32.v !var_j /\ …)` | R5.6 |
| `decreases (Int32.v !var_j + 1)` — not a counted `for`, so **the user must supply `Pal.Decreases`**; absent it, translation fails with a diagnostic | R5.9 case 3 |
| body: `let t0 = array_read var_a (Idx !var_j); array_write var_a (Idx (!var_j + 1l)) t0;` | R6.2 |
| `j--` normalised to `j = j - 1`, then `var_j := !var_j - 1l;` | R5.3 |

The result is verbose and machine-shaped. That is the point: it is what the rules produce,
not what a Pulse programmer would write. If it fails to verify, Rule 3 says the fix is a
stronger annotation in the `.cs` file or a stronger general lemma in `Pulse.Lib.CSharp.*` —
never a change here that special-cases this loop.

### 7.2 The two mechanical detectors

A derivation like §7.1 is a claim about one program. Two checks, run by `make`, are what
stop the scheme from quietly becoming a collection of per-example accommodations.

**The variant test.** Every acceptance directory ships a *second, independently worded*
implementation of the same contract, and it must verify **with no translator change**. The
variant is written to differ in every way that should not matter: `for` against `while`,
inverted branches, renamed and reordered members, `++` against `x = x + 1`, an index
computed rather than carried, a list or tree written at the *opposite null-test polarity*.
It is deliberately not a paraphrase — a variant that merely renames locals detects nothing.
This is the single most effective detector of example-fitted output, and it earns its keep
in both directions: several rules exist only because a variant found them missing (R4.14b,
F57, F58), and several apparent translator bugs turned out on inspection to be real defects
in the hand-written variant, caught by an obligation the scheme already emitted.

**The provenance lint.** `provenance-lint.sh` (R2.2) requires every top-level construct in
every generated module to trace back to a C# source span through
`source_range_info.json`. A construct with no provenance was invented by the emitter, and
under Rule 3 an invented construct must either be justified as a scheme rule or removed.

The other four lints (§8.2) check the tree rather than the scheme.

---

## 8. What is delivered

The rules above are the scheme. This section says which of them are implemented, what the
test suite asserts about them, and what is not done — in that order. It is not a changelog:
where a finding is already stated as a rule it is not restated here, and where a decision
was later reversed the reversal is recorded at the rule, not here.

### 8.1 The milestone map

Each milestone delivered a section of this document, an acceptance directory, and an
independently written variant of it (§7.2). None required a change to an earlier rule
except where noted at that rule.

| | Delivered | Section | Acceptance |
|---|---|---|---|
| M1 | Methods, contracts, statements, expressions, arrays, structs | §2–§7 | `swap` … `circular_buffer`, `insertion_sort_sorted` |
| M2 | `sealed` classes: a model, an invariant, instance methods, ownership of arrays and of other objects | §3.4, §4.5 | `counter_class`, `stack_class`, `ring_class`, `nested_class`, `deep_class`, `account_class`, `bag_class`, `interval_class` |
| M3 | Inheritance: abstract classes, virtual dispatch, upcast, checked downcast, depth *n* | §9 | `shape_hierarchy`, `deep_hierarchy` |
| M4 | Recursive data structures: linked lists, binary trees, back pointers | §10 | `linked_list`, `binary_tree` |
| M5 | User-defined specification types | §11 | `user_spec_type` |
| M6 | User-defined ownership predicates (`[Plain]`, `SlProp`) | §12 | `dll_segment` |
| M7 | Numeric conversions, side effects, and a production case study | §13 | `examples/adler32` |
| M8 | Unconstrained generics | §14 | `type_param` |
| M9 | Generic types, and generic list and tree libraries | §15 | `generic_list`, `generic_tree` |
| M10 | Separate Pulse files and typed ghost lemmas for user predicates | §12.5 | `dll_segment` |
| M11 | Cursors: iterative traversal of a linked structure | §16 | `list_cursor`, `tree_cursor` |
| M12 | `null` as a pointer rather than a wrapper | §10.2 | `linked_list`, `binary_tree` |
| M13 | `Span<T>` as a borrowed window | §17 | `array_view` |

`switch` (R5.14) arrived between M7 and M8 and has its own directory, `switch_stmt`.

### 8.2 What the suite asserts

Verification tests are the smaller half. Each of the following asserts something a
verification test cannot.

* **The variant tests (§7.2)** are the contortion detector, and every acceptance directory
  ships one.
* **`test/diagnostics`** is the negative suite: 54 cases, each headed by the diagnostic it
  must produce, each required to exit non-zero, poison `TranslationErrors.fst`, and carry a
  span in the user's own file rather than in generated Pulse.
* **`test/pulse_refusals`** is the suite that became possible once refusing was *not* the
  answer (R3.13): programs that translate cleanly, fail in F\*, and must fail for the
  stated reason on the marked line. It is indexed by *obligation kind* rather than by C#
  feature — 27 cases, and `cases/README.md` is the inventory: an index in bounds, a sum
  representable, all three parts of the loop rule separately, a measure that falls, a
  borrow given back, an invariant established by a constructor and restored by every
  method, a postcondition that has to hold on every path, and — the one the rest rests on —
  a `[Lemma]` whose body is checked rather than admitted. A negative suite grouped by feature exercises the same two obligations from a
  dozen angles and leaves whole rules untested; grouped this way the table is a claim about
  coverage that can be read and disputed. Four cases are counter-tests — the exact program
  that verified before a soundness fix — and the rest are the obligation working.

  Building it out found two provenance defects, neither of which any verification test
  could have found, because both concern *where* a true refusal is reported. `palcs report`
  preferred F\*'s `def` range over its `use` range, so an array-bounds failure was
  announced against the enclosing method's signature instead of the indexing expression;
  and the implicit `()` at the bottom of a body carried the location of whatever statement
  came last, so a postcondition failure was charged to a statement that was very often
  innocent. Both are fixed, and the cases that exhibit them — `IndexInBounds`,
  `BorrowNotReturned` — are in the suite. That is the argument for building it: a suite of
  programs that must fail is the only place a wrong *location* is visible, since every
  passing proof reports nothing at all.
* **Six lints** run in the same `make`: `no-example-names.sh` forbids any acceptance
  directory or method name from appearing in `Pal.Compiler`; `provenance-lint.sh` (R2.2)
  requires every top-level construct in every generated module to trace to a C# span;
  `diagnostic-ids.sh` keeps the analyzer's declared ids in step with the passes that raise
  them; `fst-configs.sh` and `cs-projects.sh` keep the editor's view of the tree in step
  with the build's; `ide-build.sh` requires every test project to compile clean *with the
  analyzer loaded*.
* **Every test directory compiles as stock C#.** `test/build-cs.sh` synthesises a plain
  project — deliberately not one that loads pal-csharp's analyzer, since a project that did
  would no longer be checking the thing that matters. This is the core invariant asserted
  against the C# compiler rather than against a document.

### 8.3 Findings that are not rules

Recorded here because they generalise and have nowhere else to live.

* **A `[Spec]` predicate used in a loop invariant must be total.** A `[Requires]` on a
  `[Spec]` predicate becomes a refinement on its last binder (R4.6), and that refinement
  must then be discharged wherever the predicate appears — including at invariant
  *establishment*, where the counter is often out of range (`i = 1` on an empty array). So
  `Sorted`, `AllAbove` and `Dominated` take no `[Requires]`; the index bounds go into the
  quantifier's antecedent, from which well-typedness of `s[i]` follows. This is the single
  most common cause of a failed invariant that looks like a prover problem and is not.
* **Pulse matches resources syntactically, which constrains the emitter twice.** A local
  that owns something is initialised *into its own binder* rather than aliasing a temporary
  (F77; R12.4 for allocation, R17.5 for a span borrow). And only the *receiver* of a
  class's own methods is unfolded — an object that merely passes through stays folded,
  because every function taking it expects its invariant and not its representation.
* **An analyzer must run the emitter too.** Stopping at the checker looks right, since an
  editor has no business writing files, but eight of the diagnostics — R5.3's unbridgeable
  type, F3's measure over an existential, an unsupported specification term — are only
  discovered while emitting. An analyzer reporting the rest would be worse than none: it
  would tell a user who had cleared every squiggle that the program was ready, and the
  build would disagree. Parity is cheap, because emission is string building over an IR
  already in hand; the output is thrown away.

  The gap was found by wiring, not by `test/analyzer`, which is the more useful lesson: a
  hand-picked case set is exactly what fails to notice a whole pass going unrun. The test
  now requires every directory of `Pal.Compiler` that raises an id to be represented among
  its cases.
* **What Pulse said must arrive, not be recomputed.** An analyzer cannot run a prover, but
  it can read the last answer, and Roslyn has a sanctioned way to depend on a file:
  `AdditionalFiles`, which it tracks and re-runs analysis over. `palcs report` writes
  `verification.txt` (R2.3) and the analyzer reports each message at its mapped C# span. An
  analyzer that opened the file itself would read something Roslyn does not know it depends
  on, so the result would cache against a key that omits it and the squiggles would go
  quietly stale — the one failure mode worse than having none.
* **Two views of one resource are the limit** (F27): a third makes Pulse's matcher
  ambiguous, so more observers are reached by nesting share/use/gather. Relatedly, Pulse
  does not split a permission at a call site (F25), for objects or for arrays — which is
  why R4.9's claim since M1 that "the same array may be passed to two parameters at once"
  was unreachable until R5.13's `Pal.Share`/`Pal.Gather` existed.
* **A model-level fact is unreachable from inside an invariant** (F17), and fails much
  later, in an unrelated client file. `PALCS0527` refuses an `[Invariant]` clause that
  mentions no field for this reason — a diagnostic whose whole value is moving a failure to
  where it can be understood.

### 8.4 The inheritance studies: the probe record for §9

§9 is the scheme; this is what it was derived from. Before any C# surface for
`abstract`/`virtual`/`override` was proposed, the encoding was worked out **directly in
Pulse** and verified end to end: `test/pulse_facts/ShapeHierarchy.fst` is a complete
`Shape`/`Circle`/`Square` hierarchy with a heterogeneous `Shape[]`, and
`test/pulse_facts/InheritanceFacts.fst` pins the facts (F28–F34) it rests on. Every
construct carries the C# it stands for in a comment.

It is kept because §9's restrictions are only intelligible against it: each of R9.2, R9.3
and R9.4 is a refusal to translate something the studies did not probe, and this is the
record of what they did.

The encoding, in one line: a class is a **vtable record** carrying its representation
type, its invariant and its methods, and an object is that record paired with its
representation, **lowered to `Type0` through `FStar.Dyn`**.

| C# | Pulse | Cost |
|---|---|---|
| `abstract class Shape` | `t_shape`, a record of `impl: Type0`, `inv: impl -> perm -> model -> slprop`, and one field per virtual member | — |
| a `Shape` reference | `shape = FStar.Dyn.dyn`, i.e. `Type0` — so it is boxable, arrayable, and a legal field | one axiom (below) |
| `shape__inv s #p m` | `exists* o. pure (s == mkdyn o) ** o.pkg.inv o.rep p m` | — |
| `class Circle : Shape` | a concrete invariant `circle__inv` plus a packaged `t_circle` | both faces are needed |
| `Circle`'s own model | its own record, plus a pure forgetful map to `Shape`'s model | F17 one level up |
| `override int Area()` | a field of the vtable | — |
| `s.Area()` | project the slot, **let-bind it**, then apply | F31 |
| upcast `Shape s = c;` | a `ghost fn` | free at runtime, as C# requires |
| `new Circle(r)` | a *static* `fn`: allocate, fold the concrete invariant, upcast | a constructor is not a vtable slot |
| `Shape[] a` | `A.pts_to a sq ** forall+ k. shape__inv sq[k] #p ms[k]` | `Pulse.Lib.ForEvery.Range` |
| `Pal.Share(s)` / `Pal.Gather(s)` | `stt_ghost` vtable slots | ghost, so aliasing a `Shape` is free |

Five findings that the study settled, each of which would otherwise have been guessed:

1. **The model may not be fixed per hierarchy.** A subclass keeps its own model and
   supplies a pure forgetful map; the base invariant is
   `exists* cm. sub__inv c #p cm ** pure (forget cm == m)`. This is exactly R3.9's
   abstraction function, applied one level up.
2. **`share`/`gather` are not derivable from `inv`** — how a permission distributes over
   an object's parts is the implementation's business — so any hierarchy that supports
   read-only aliasing must carry them in the vtable. They can be `stt_ghost`, and a
   `ghost fn` can project the ghost package and run them, so R3.10e's aliasing story
   survives inheritance at zero runtime cost. This was the main open question and it
   resolved favourably.
3. **`gather` forces a ghost index.** Two views of one `Shape` unfold to two *separate*
   existential witnesses, related only by `s == mkdyn o1` and `s == mkdyn o2`; concluding
   `o1 == o2` is injectivity of `mkdyn`, which is Cantor-inconsistent and which
   `FStar.Dyn` therefore omits. The fix is not another axiom but an extra ghost index —
   `shape__inv_at s o p m` names the implementation package, so two views are at the same
   `o` by construction. `shape_gather_unindexed` is pinned as an `expect_failure` and
   `shape_gather_at` verifies. This also states something true: a CLR object's dynamic
   type is fixed for its lifetime. **Methods must therefore be stated at the indexed
   invariant and the plain form derived**, because a client that passes through the plain
   form loses the index and can never gather again.
4. **A mutating traversal cannot borrow.** `total_area` borrows each element with
   `range_focus` and closes the trade; `double_all` cannot, because the model changes and
   the trade will not close, so it carries two ranges and peels/appends. Both verify.
5. **`null` is a real open problem.** `new Shape[3]` fills with `default(Shape)`, of
   which no object invariant holds. The study allocates with a `null_shape` placeholder
   and immediately overwrites every slot; a C# surface needs either definite-assignment
   analysis over array initialisation or an explicit `null` model.

**The one thing assumed** is `recover`, which belongs in `Pulse.Lib.CSharp.Assumptions`
but in its own section, because unlike `SizeTFitsU32` it is a *computation*, not a
`Lemma`:

```fstar
val recover (#a: Type u#a) (#x: erased a) (d: dyn { d == mkdyn (reveal x) })
  : stt a emp (fun y -> pure (y == reveal x))
```

*The CLR object header faithfully records the dynamic type.* It is needed because
ownership is about a *particular* value: without `y == x` you hold a well-typed reference
owning nothing, and the proof does not fail conservatively — it does not go through. It
is unprovable rather than merely unstated, since `FStar.Dyn.undyn` returns in `Dv` and
`Dv` results cannot be equated in specifications (F30). Stating it in `stt` rather than
`stt_div` matters: `stt_div a emp post` is inhabited for *every* `post` (F30b, verified
by a hang), so an `stt_div` axiom would be free and worthless, and F2 already requires
every emitted `while` to carry `decreases` precisely to stay in `stt`. It does **not**
imply injectivity of `mkdyn`, because each `recover` is a separate computation — which is
why finding 3 above is a genuine constraint and not a consequence.

**Consequences, and what §9 did with them.** A class needs *both* faces — a concrete
invariant for its own methods (R4.10) and a package for its clients — and the choice had
to be **pay-as-you-go**, since a `sealed` class must keep M2's translation verbatim or the
"textually additive" property is lost. §9 is that choice, and R9.1 is where it is drawn.
The cheaper alternative was a **closed-world sum of representations** over a hierarchy
whose subclasses are all in the compilation, needing no axiom at all; it was rejected
because it supports neither separate compilation nor open extension.

The study's closing recommendation — do **interfaces first**, where there is no
representation to inherit and no `base` call to model — was not followed, and §8.6 records
why: an interface adds *multiple* implementation, which R9.8 pins as hard, and the
motivating example needs ownership in a virtual method's signature (R9.9a), which is a
separate problem again.

#### Depth three: `test/pulse_facts/DeepHierarchy.fst`

The two-level study leaves the central question of inheritance untouched, because a
leaf class is only ever a subclass. `DeepHierarchy.fst` is the same encoding taken to

    Shape
     +-- Circle
     +-- Quadrilateral            (abstract, with methods of its own)
          +-- Square
          +-- Rectangle

so that `Quadrilateral` is a subclass *and* a superclass at once: it is packaged into
its parent's vtable and is itself a vtable that further classes instantiate. It
verifies, including a heterogeneous `Shape[]` whose elements sit at two different
depths, a client written against `Quadrilateral` that names no leaf class, and an
end-to-end `demo` proving the concrete result `66`.

Three things had to change, and each is a finding.

1. **The reference is always `mkdyn`'d at the root's object record.** A dyn is made at
   exactly one witness type, so a value made at `quad__obj` can never be viewed as one
   made at `shape__obj` — that is `mkdyn` injectivity again, which finding 3 above rules
   out. An upcast therefore cannot rebuild the dyn, and `Quadrilateral` cannot have a
   reference type of its own. `quad` and `shape` are the *same* F\* value; only the
   invariant differs, which is exactly the C# semantics of a reference conversion.
2. **The root object record needs one extension point**, a single `sub: Dn.dyn` field
   that `Shape` declares and says nothing about. An intermediate class stores its own
   object record there and its own invariant says what is in it. This is what keeps the
   scheme open-world: `Shape` is compiled once and admits subclasses that do not exist
   yet, which a sum over the known subclasses would not. It hangs off the *object*, not
   the vtable, because what a descendant must recover is a vtable already applied to a
   representation — recovering a bare vtable would leave its `impl` only propositionally
   equal to `pkg.impl` and every use would need a coercion.
3. **An intermediate vtable lists every method visible at its level**, inherited ones
   included, read at *its* model — as a real vtable re-lists the slots it inherits.
   That is what lets a `Quadrilateral`-typed reference call `Area()` and keep its
   bounding box, which a client that upcast to `Shape` and back could not. The four
   inherited slots are then derived **once**, generically, by `quad_as_shape_pkg`, so
   `Square` and `Rectangle` implement the quadrilateral vtable only and get their
   `Shape` vtable for free. That derivation is what "inherits" means here.

Dispatch at level *k* costs *k* recoveries — one to reach the root object, one per
`sub` hop — and each is a cast on the same reference. F31's let-binding rule applies at
every hop.

Two further findings came out of writing it.

* **A virtual method's precondition, written at the base model, must be strong enough
  for every subclass's model.** `Shape.Double` requires `ok32 (4 * Area)`, and from that
  a quadrilateral can prove its *bounding box* doubles safely (`2*W <= 4*W*H` when
  `W, H >= 1` — the same argument `double_fits` makes for a radius), but it cannot prove
  anything about a *perimeter*: isoperimetry gives `P^2 >= 16*A` and no upper bound at
  all, so a 1-by-n rectangle has perimeter about twice its area. `Quadrilateral`'s model
  is a bounding box for exactly this reason. Where a subclass genuinely needs more, the
  base must either state the precondition abstractly (a vtable-supplied predicate over
  the representation) or expose a virtual query — `if (s.CanDouble()) s.Double();`. A C#
  surface should push users towards models whose quantities are bounded by the base's.
* **A non-virtual method of an intermediate class needs nothing new.**
  `quad_semi_perimeter` calls the virtual `Perimeter()` on its own receiver and is an
  ordinary `fn` over `quad__inv` — no vtable slot, no recovery of its own, and it works
  for subclasses written later. This is also the first place in either study where a
  method calls a virtual method on `this`, which was on the not-probed list; it is
  settled, and settled by R4.10 doing nothing special.

**An *unchecked* downcast is impossible; a *checked* one needs no new assumption.**
`§13` pins the first as `downcast_is_not_free`: holding `shape__inv s #p m` says `s` is
some root object and says nothing about whether it is a quadrilateral, because the
information was discarded by the existential when the reference was upcast, which is
what an upcast means. `§14` then supplies the second.

Be precise about what "checked" means here, because it is *not* "we prove the runtime
test succeeds". `recover` has no failure mode — it is not "test the header and maybe
fail" but "given a proof the header matches, hand back the value", its argument refined
by `d == mkdyn x`. `quad__inv_at` carries that refinement at each hop, so the cast
cannot fail; but it cannot fail because the encoding only lets you *write* the casts
whose test is redundant. A cast that might fail is not one this study proves safe, it is
one this study cannot express. That is the right stance for a verifier — a verified cast
is one that cannot throw, consistent with exception-freedom (§6) — but it is a
restriction on the source language, not a theorem about C#.

Nor is the cast free at *runtime*: depth `k` costs `k` recoveries where the CLR does one
header check. What is free is the **proof**, and the details are:

* **The precondition *is* the knowledge, and it is the ghost index `gather` already
  forced.** `quad__inv_at s qo p qm` names the object record; `downcast_square` requires
  it at `square__obj c` and returns `Square`'s own invariant plus `r == c`. This is not
  a coincidence: `gather` needs a client to know *which* implementation the two halves
  came from, and a cast needs it to know *which* implementation it is narrowing to. Both
  are satisfied by remembering rather than by testing, which is why the checked cast
  costs no axiom. A constructor that keeps the index (`new_square_at`) and one that
  forgets it (`new_square`) are the same code plus one ghost step.
* **The indexed method is the primitive and the plain one is derived.** `quad_area_at`
  dispatches; `quad_area` is `quad_area_at` composed with `quad_forget_impl`. Indexing
  therefore costs nothing in expressiveness — a client that never downcasts forgets at
  every call — and a C# emitter can generate one dispatching body per virtual method,
  not two.
* **Forgetting is irreversible even to a client that can say what it forgot.**
  `quad_remember_impl` is pinned `expect_failure`: from `quad__inv s` you get an
  anonymous `qo'` with `s == mkdyn (shape_view qo')`, and equating it with a known `qo`
  is `mkdyn` injectivity. So an upcast is a real, one-way commitment, and the C# reading
  is exact — a `Quadrilateral`-typed variable carries no static evidence of its dynamic
  type.
* **A checked cast is a chain of recoveries, one per level**, because each level's
  object record is a distinct value: `quad_rep` recovers the root object, follows `sub`
  to the quadrilateral object, and re-boxes its representation with
  `quad_box qo = mkdyn qo.qrep` so that congruence — not a `coerce_eq` across a merely
  propositional type equation — delivers the equality the final `recover` wants. The CLR
  does the whole thing with one header check; that gap is the price of erasing the
  dynamic type into `dyn`, and it is paid in casts, not in memory.
* **`is` is a proposition, and only ever a positive one.**
  `is_square qo = exists (c: square). qo == square__obj c`; `as_square` turns it back
  into the named index by classical choice, free and ghost. The negative direction is
  *not* available — `a_rectangle_is_not_a_square` is pinned `expect_failure`, since F\*
  cannot generally refute an equation between values of two abstract representation
  types. That is sound (the caller still cannot cast) and is the right shape: what makes
  a cast safe here is a positive record of the construction, never the failure of an
  attempt to disprove it.
* **A *failing* cast is still out of reach**, per the caveat above: `q as Square`
  returning `null`, or a checked cast throwing, is a runtime test whose *negative*
  answer must be trusted, and would need `recover` strengthened to report a mismatch.
  Nothing in either study needs it and it is not assumed. A C# surface therefore has a
  real choice to make — reject `as` and failing casts outright, or admit them and pay
  for the stronger axiom.

Still not probed, and still to be probed before any rule admits them — these are exactly
the restrictions R9.2, R9.3 and R9.4 impose: `base.M()`; `protected`; a class that
overrides some methods and inherits others (every class in the studies supplies a *full*
vtable, which is correct but says nothing about building one from a partial `override`
list); an `abstract` class with fields, and hence a constructor chain; a class holding a
`Shape` *field* (boxable per F29, but nested-invariant composition à la R3.10b is
untested); and a cast that may fail.

### 8.5 Not yet done

**Language constructs outside the subset.** `string` and `float`/`double`; `interface`
declarations; *constrained* type parameters (§14 delivers unconstrained ones, and §14.4
says why a constraint is a typeclass obligation rather than a syntactic one);
`IEnumerable<T>` and `foreach`; delegates and lambdas in executable position; `async`;
`goto`; `try`/`catch`/`throw`; `Memory<T>` and `ArraySegment<T>` (§17.5); `stackalloc`
(R17.7); a non-tail `return` **inside a loop** (R5.5b reaches every other position); and a
`switch` label that is a pattern or carries a `when` guard.

**Gaps in the scheme, each with its reason.**

* **A struct field must be a value** — a scalar or another translated struct. An array or
  class field is `PALCS0511`, and that is the model rather than a shortcut: a struct copy
  would duplicate ownership of the same memory. Storage travels alongside the state it
  describes. A *class* has no such restriction (R3.10a, R3.10b), which is why
  `test/stack_class` is what `test/circular_buffer` wanted to be.
* **Object abstraction is deliberately deferred.** `class_C__inv` is a *concrete*
  definition in the class's own module. Hiding it behind an `.fsti` works and needs no F\*
  `friend`, but requires a module shape the emitter does not have, and C# `private` already
  hides the representation at the source level. Available when proof performance or genuine
  information hiding demands it.
* **An object may not be allocated in a block that closes around it** (R4.14a,
  `PALCS0001`). F19 is a limitation of Pulse's inference, not of the scheme, and the
  workaround — allocate in the method's block, or in a branch that returns — is usually
  what the code wanted. `test/ring_class/RingScope.cs` covers what does work.
* **Object lifecycle is unspecified.** A class with two-phase initialisation or `Dispose`
  wants a *state*-indexed invariant, `class_C__inv this st m`, and nothing has one.
* **Reference identity** — `ReferenceEquals`, and `==` on a class — has no story. `Box`
  supports equality, but nothing relates it to the ownership discipline.
* **A field is not nameable in a spec position outside a loop or a ghost statement.**
  R5.11a and R5.12 bind `this.f` where the emitter has just named the representation; a
  `[Requires]` or `[Ensures]` reads against the model (R3.9c), which is right. There is no
  third context, and nothing has wanted one.
* **A postcondition cannot say why a loop stopped.** R5.10's break flag is internal to the
  translation, so an invariant cannot mention it, and a contract needing "the loop ran to
  completion" is unstatable — see `test/compare_elements`, whose `Equal` carries its exit
  condition in the guard for this reason. PAL's answer is a per-`break` `_ensures`, and the
  C# surface would be a `Pal.Ensures(Q)` leading a `break`.
* **`out` is modelled exactly as `ref`** — `pts_to` at both ends, not `pts_to_uninit`
  strengthening to `pts_to` — so a caller must initialise an `out` argument before the
  call. Sound, but it demands more than C# does.
* **A ghost argument determined only by the pure part of a contract cannot be passed at a
  call site** (R4.5): ghost arguments are resolved by unification, and there is no
  zero-cost C# surface for explicit implicit application.
* **Heterogeneous arrays** — an array whose element type is a base class — need §6's array
  rules to carry an object invariant per element, which the studies do in Pulse
  (`Pulse.Lib.ForEvery.Range`) but §6 has not probed.
* **A recursive user-declared spec type** whose constructor takes the type being declared
  is refused (§11); the induction is not the difficulty, the `[Model]` binding is.

**Tooling.**

* **The analyzer is not a NuGet package.** It is wired into `test/analyzer` as `Analyzer`
  items, which is enough to run and to test it, but a user must point at the built
  assemblies. A package must also carry `System.Text.Json` and `System.Memory` for a .NET
  Framework host, where they are not in the shared framework.
* **Live squiggles are per-compilation work.** The analysis is whole-program — a call needs
  its callee's contract — so it runs once per compilation and is reported per file. On the
  programs in `test/` that is milliseconds; nothing has been measured at a scale where it
  would not be.

### 8.6 What is next

Three candidates, in the order the evidence puts them. All three are on §14.4's rejection
list, and all three appear in the upstream code `examples/adler32` was ported from, whose
`Adler32 : IChecksum` needs an interface, a generic struct and a property at once.

**Constrained generics.** §14 delivers the element-agnostic part of the language —
segments, spans, copies, swaps, containers — which is what the case study wanted, and §15
delivers generic types. What is left is the *constraint*: `where T : IComparable<T>` is a
typeclass obligation, and a generic sort or an ordered container cannot be written without
it. This is the smallest of the three and unblocks the most library code.

**Interfaces.** An interface is very nearly what §9 already has: R9.2 requires an abstract
class to have no fields and R9.3 requires its virtual methods to be abstract, which is the
definition of an interface. What a C# `interface` adds is *multiple* implementation, and
R9.8 pins why that is hard — a `dyn` is made at one witness type and `mkdyn` is not
injective, so one value cannot be viewed at two unrelated roots. But the blocker for the
motivating example is elsewhere and is worth naming: `IChecksum.Update(byte[] buffer)`
takes an array, and **R9.9a restricts a virtual method to plain values**. Interfaces would
therefore deliver the declaration without delivering `IChecksum`; the real prerequisite is
ownership in a virtual method's signature, which is its own design problem.

**`IEnumerable<T>` and `foreach`.** §16's cursors are the manual form of this, and they
verify; what is missing is the surface. A `foreach` over a cursor is a loop whose invariant
mentions a position the user did not write, so the interesting question is whether R5.8's
invariants can be stated about an iterator without the user naming its state — which is
§16.5's open question, now with §17's answer available as a precedent: where a proof step
has no C# spelling, give the author one rather than inferring it.

**Strings, cheaply, whenever.** F65 records that the encoding is nearly free: a string is
immutable, so there is nothing to own, and it is a pure value under `requires emp` where an
array parameter costs a `pts_to` at both ends. Strings are not deferred because they are
hard but because the cost is not in the model at all — it is the library surface
(`Substring`, `IndexOf`, `Split`, concatenation, formatting), each item of which is an
obligation with a specification to get right.

---

## 9. Inheritance

§8.4 records two design studies — `test/pulse_facts/ShapeHierarchy.fst` (depth two) and
`test/pulse_facts/DeepHierarchy.fst` (depth three) — in which the encoding below was
probed before any of it was written down. This section turns those studies into rules.
Every construct named here appears in one of the two studies; nothing is invented.

### 9.1 What is in scope, and why the boundary is where it is

M2's class encoding (§3.4) is a `Box.box` of a record. That encoding admits no
subclassing at all: the representation type is fixed by the reference type, so a
`Shape`-typed variable would have to have *one* field layout. Dispatch needs the
representation to be existential, and that is the whole reason M3 looks different.

**R9.1 — A class is in a hierarchy iff it is `abstract`, or its base list names a
translated class.** A `sealed class` with no base list is M2 and its emission does not
change by one character. This is a genuine fork, and it is drawn by the C# declaration
rather than inferred, so a user always knows which encoding they are getting.

Three restrictions on the *encoding* — none of them, any longer, a restriction on the
input. §9.11's desugaring puts an arbitrary hierarchy into this shape, so what follows
describes what the emitter is handed rather than what a user may write:

* **R9.2 — An abstract class has no fields.** The studies give `Shape` and
  `Quadrilateral` no representation of their own; the representation is entirely the
  leaf's. A base field would make the leaf's representation an extension of the base's and
  force a constructor chain. R9.21 supplies neither: it gives the fields to a generated
  leaf and replicates them into each subclass's leaf, so no representation is ever an
  extension of another.
* **R9.3 — Every virtual method on an abstract class is `abstract`.** In both studies each
  leaf supplies a *full* vtable. A `virtual` method with a body would have to be inherited
  by a subclass that does not override it, and a base method body can only run against a
  representation the base does not have. R9.21 supplies the missing representation — the
  body moves to the leaf that has one — and R9.21b replicates it into each subclass's
  leaf. `base.M()` remains refused: it names a *particular* body rather than a slot, and
  after the split the body it names is on a sibling leaf, not a base.
* **R9.4 — A concrete class in a hierarchy is `sealed`.** A non-sealed concrete class is
  both a vtable *value* and a vtable *type*. R9.21 splits it into one of each.

A non-`abstract` method on an abstract class is *not* refused: it is an ordinary method
over the class's invariant, dispatching through its own receiver like any other client
(`quad_semi_perimeter` in the study). This is the C# `sealed`-by-default reading and it
costs nothing.

### 9.2 Models and the forgetting function

**R9.5 — An abstract class's `[Model]` member is `abstract`, and declares only the model
*type*.** It has no body because there is no representation to abstract from. Its
`[Refine]` clauses behave exactly as in R3.9d.

**R9.6 — A derived class supplies its parent's model by `override`ing the parent's
`[Model]` member with an expression over its *own* model.** That override *is* the
forgetting function, and it is written in idiomatic C# with no new attribute:

```csharp
public abstract class Shape          { [Model] protected abstract SpecInt Area { get; } }
public sealed class Square : Shape
{
    private int side;
    [Model] private SpecInt Side => side;              // abstraction from the fields
    protected override SpecInt Area => Side * Side;    // Shape's model from Square's
}
```

Emitted as `class_Square__forget (m: class_Square__model) : class_Shape__model`. It is a
total function of the derived model, which is what makes a subclass a *refinement* of its
parent: the parent's model is recoverable from the child's, and never the reverse.

**R9.6a — The abstraction function and the forgetting function are two members.** R9.5's
reads the *fields*; R9.6's reads this class's *model*. They have different domains, so one
member cannot be both, and marking the `override` itself `[Model]` asks it to be. That is
refused on the declaration (**PALCS0543**) — not a claim about what Pulse could prove, but
a statement that the translator has no rule for a single expression read against two
different scopes.

It is worth recording what it looked like before the refusal existed, because it is a
pattern to watch for elsewhere: the request was *accepted*, and the same syntax node was
lowered twice — once against the fields, which succeeded, and once against the model, which
did not. What the reader saw was `PALCS0001: the expression 'side' is not supported`,
pointing at a field that is perfectly supported. One node serving two roles is the same
shape of defect as R4.11c's one question answered twice; here it produced a useless message
rather than a false postcondition, but the cause is the same and so is the fix.
`test/diagnostics/cases/ModelIsForget.cs` is the case.

**R9.7 — A virtual method's contract is written once, on the `abstract` declaration, at
the declaring class's model.** An `override` carries no contract of its own; restating it
would be either a repetition or a Liskov violation, and C# gives it nowhere to go. So the
*implementation* in a leaf is checked against the parent's contract, over the parent's
model — which is exactly how the studies type a leaf's vtable slots.

This has a consequence worth stating because it is the most common way a hierarchy fails
to verify: **a base method's precondition must be strong enough for every subclass.**
`Shape.Double()`'s `4 * Area <= int.MaxValue` bounds a square's side only because a
square's area is `side * side`; for a shape whose model does not bound its representation
the base precondition says nothing and the leaf will not verify. §8 works this out for a
quadrilateral's perimeter. The fix is the user's — strengthen the base contract, or add a
`[Refine]` to the leaf's model — and never the emitter's.

**R9.7a — A virtual method's parameters are in scope in its contract.** R9.9 admits value
parameters on a slot and all three wrappers emit a binder for each, so the missing half was
only that the scope a contract is read in bound `@this` and nothing else. `Result == k *
@this.TheArea` was rejected as **PALCS0300**, `k cannot be mentioned in this
specification` — a virtual method could take an argument it was forbidden to say anything
about, which is no use at all.

The binding itself is the simple case, and R9.9 is why: a slot's parameters are machine
integers and booleans passed by value, so there is no cell to read through and nothing
changes across the call. One term serves the pre-state and post-state scopes, under the
same name the wrappers bind, and `Old(k)` needs no special case because it cannot differ
from `k`. A parameter that *was* a resource would need all of that, and R9.9's PALCS0545
is what keeps one out of a slot.

This is the second gap the R9.12b audit turned up, and it was found the same way, so the
method is worth recording. R9.12b was one empty cell in a two-by-two — a virtual method
that mutates *and* returns. Asking what *else* the suite never wrote about a virtual
method answered immediately: **every virtual method in every test was nullary**. Both gaps
were invisible for the same reason and neither was a hard problem once written down.
**A generated construct is only as tested as the shapes of source that reach it**, and the
cheap way to find the untested ones is to tabulate the axes an emitter branches on and
look for the empty cells, rather than to re-read the emitter.

### 9.3 What a reference is

**R9.8 — A reference into a hierarchy is a `dyn`, and the dyn is always made at the
*root's* object record.** `class_Shape = Dn.dyn`, and so is `class_Quadrilateral`: an
intermediate class is a *view* of the same value, differing only in its invariant. This
is exactly C#'s reference-conversion semantics, and it is forced — a dyn is made at one
witness type, so a value made at `class_Quadrilateral__obj` could never be read back as a
`class_Shape__obj` without injectivity of `mkdyn`, which `ShapeHierarchy.fst` §3 pins as
unavailable.

**R9.9 — Each abstract class emits a vtable type, an object record, an ownership
predicate, and an invariant**, in that order:

| Construct | Meaning |
|---|---|
| `class_C__vtbl` | one field per virtual method visible at `C`, at `C`'s model, plus `impl: Type`, `inv`, `share`, `gather` |
| `class_C__obj` | `{ pkg: class_C__vtbl; rep: pkg.impl; sub: Dn.dyn }` — `sub` is R9.18's extension point |
| `class_C` | `Dn.dyn` at the root; the parent's reference type at an intermediate class (R9.18) |
| `class_C__at o p m` | `o.pkg.inv o.rep p m` — ownership of a *known* object record |
| `class_C__inv s #p m` | `exists* o. pure (s == mkdyn (view o)) ** class_C__at o p m` |
| `class_C__inv_at s o p m` | the same with the object record **named** |

`class_C__inv` has the same signature as an M2 class invariant (§3.4), which is why a
*client* of a hierarchy needs no new rules at all: R4.5's model binders, R4.10's
fold/unfold bracket, R3.10b's nested objects and R5.12's loops all apply unchanged.

A slot's type is the virtual method's contract with the receiver read as the vtable's own
`inv x p m`. Three things about it are load-bearing, and all three were found by building
it rather than by reading the studies:

* **R4.8 applies to a slot exactly as it applies to a method.** A slot's `ensures` is
  `pure (REQ ==> ENS)`, because that is what the `Func_` module implementing it produces
  and one C# contract must not be stated two ways. Emitting the bare `ENS` in the slot
  makes the vtable literal fail with an unprovable subtyping check, which is the right
  failure: the two are not definitionally equal even though they are equivalent.
* **A slot is generated apart from `MethodPlan`.** Its `inv` takes the permission
  *positionally* where R4.10's takes it as F21's meta-argument-defaulted implicit, so the
  application shapes differ and there is nothing to share.
* **The binder orders differ, and the eta-expansion is where they meet.** A slot binds
  `#p` before `#m`; R4.10 threads the model binder before R4.11b's permission. F33 already
  forces the pack site to eta-expand every slot, so the reconciliation costs nothing and
  neither side bends towards the other.

**R9.9a — A virtual method takes and returns plain values.** A slot's type is fixed by the
base class, so every subclass would have to own the same resource in the same way; only a
value parameter has a reading that does not depend on the implementation. An `abstract`
method with an array, object or `ref` parameter is refused (PALCS0545) rather than given a
guessed ownership.

**R9.9b — Inside `Class_C`, an observation of `C` is written unqualified.** This is R3.7's
rule about field qualifiers, and it holds for the same reason: a self-qualified name makes
F*'s dependency scan read the module as depending on itself. It first bites here because
§3.4's class module has no reason to mention its own observations, and a vtable slot's
contract has every reason to.

**R9.10 — The indexed invariant is the primitive; the plain one is derived.** Both
studies force this. `gather` needs to know *which* implementation the two halves came
from, and so does a downcast (§9.7); `class_C__forget_impl` throws the index away, and is
one ghost step. Every dispatching wrapper is emitted at the index, with the plain form
derived — one dispatching body per method, not two. Forgetting is *irreversible* even
given the equation (`quad_remember_impl` is pinned `expect_failure`), so an upcast is a
real one-way commitment, which is the honest reading of C#.

**R9.11 — `share` and `gather` are vtable slots, not emitted lemmas.** R3.10d emits them
per class because their proofs recurse into the class's own structure. Behind a dyn there
is no structure to recurse into, so they become dispatched operations like any other, and
the leaf supplies them from the R3.10d bodies it already has. Read-only aliasing of a
`Shape` therefore costs nothing at runtime.

### 9.4 Dispatch

**R9.12a — A call is virtual iff it resolves to an `abstract` declaration**, however the
receiver is written. It is emitted as the dispatching wrapper in `Class_C`, and its
arguments, implicit model binder and permission are found by exactly the rules a direct
call uses, because R9.9 gives the wrapper the same contract shape a direct method has.

**R9.12 — A call on a hierarchy-typed receiver dispatches through the vtable, and costs
one `recover` per level.** For a root-typed receiver:

```
fn class_C_M_at (s: class_C) (#o: erased class_C__obj) …
  preserves class_C__inv_at s o p m
{ unfold …; let ob = recover #class_C__obj #o s; let f = ob.pkg.fld_M; let v = f ob.rep …; fold …; v }
```

Three facts from §1 are load-bearing here and the emitter obeys all three without knowing
why: F31 (a stored Pulse computation must be let-bound before it is applied — `ob.pkg.f x`
does not run), F33 (a pack site must eta-expand every slot, because F21's
meta-argument-defaulted permission binder does not match a vtable field type), and F34
(name the body of an invariant so that the closing `fold` has a head symbol whose argument
*is* the witness).

At depth *k* the wrapper recovers the root object and then follows `sub` once per level.
The CLR does the whole thing with one header check; the gap is the price of erasing the
dynamic type into `dyn`, and it is paid in casts, not in memory.

**R9.12b — A dispatching wrapper binds the slot's result exactly when the slot has one,
and returns it after the invariant is folded back.** Stated this baldly the rule sounds
like it needs no stating, and for two years it was left implicit. It was implemented only
on the read-only path.

The two paths differ, and the difference is why: a read-only wrapper ends in
`fold (…__inv_at s o p m)` with the *same* model it started with, whereas a mutating one
must first name the post-model the callee produced —

```
let f = ob.pkg.fld_M;
let v = f ob.rep …;                                  // R9.12b: bound because M returns a value
with post_this. assert (ob.pkg.inv ob.rep p post_this);
fold (class_C__at ob p post_this);
… ;
v                                                    // R9.12b: after the fold, not before
```

— and the extra `with`/`assert` between the call and the fold made the mutating path look
like a *statement* sequence, so the value was dropped on the floor. `fold` returns `unit`,
so the wrapper declared `returns ret: I32.t` and its body ended in `()`.

That combination — a virtual method that **both** mutates its receiver and returns a value
— is unremarkable C# (`int Bump() { int was = k; k = k + 1; return was; }`) and was inside
the shipped subset the whole time. Nothing rejected it. `palcs` reported `0 error(s)` and
wrote ill-typed Pulse, which is the failure §18 exists to prevent: the emitter must either
translate a construct or refuse it, and *silently mistranslating* is worse than either.

Three wrappers are subject to the rule and all three had the defect, which is itself the
lesson — R9.10 emits two (the indexed form that dispatches and the plain form that composes
it with forgetting, where the intervening `__forget_impl` is ghost and returns `unit`), and
R9.18 emits a third for each intermediate class (the forwarder that packages that class's
vtable into its parent's, where the intervening step is a `fold` again). Each was written
at a different time and each independently grew a `moves ? … : …` split around the call,
and in all three the value-binding — which has nothing to do with whether the receiver
moves — got captured by that split. **A conditional in the emitter attracts unrelated code
into its branches**; when the same two-armed test appears at three sites, what is common to
the arms deserves to be lifted out of the test rather than duplicated into it.

The regression test is `test/deep_hierarchy`'s `DoubleAndReport`, dispatched at the root
over a leaf of the intermediate class so that all three wrappers are on the path at once.

**R9.13 — `recover` is the one assumption.** `Pulse.Lib.CSharp.Assumptions.recover` says
the CLR object header faithfully records the dynamic type. It is unprovable because
`FStar.Dyn.undyn` returns in `Dv`, and it is stated in `stt` rather than `stt_div` because
`stt_div a emp post` is inhabited for every `post` and so would assume nothing. It does
**not** imply injectivity of `mkdyn`.

### 9.5 The leaf

**R9.14 — A `sealed class C : P` emits its M2 representation *unchanged*, plus five
things**: the forgetting function (R9.6); `class_C__as_P`, which is `class_C__inv` seen at
`P`'s model; one `fn` per `override`, specified over `class_C__as_P` and `P`'s model
(R9.7); the vtable literal `class_C__vtbl : class_P__vtbl`; and
`class_C__obj (c: class_C) : class_P__obj`.

That the leaf's own invariant is untouched is the point: an M2 class and an M3 leaf differ
by a wrapper, so `[Invariant]`, `[Refine]`, arrays, nested objects and R3.10d's share and
gather all keep working inside a hierarchy with no new rules.

The vtable literal must be emitted *after* the method modules and *before* the
constructor's, so it gets a module of its own, `Vtbl_C.fst` (§2). F* computes the order.

### 9.6 Upcast

**R9.15 — An upcast is a ghost fold, and is inserted where C# inserts a reference
conversion**: assignment to a base-typed variable or field, an argument to a base-typed
parameter, a `return` at a base type, and an element store into a base-typed array.

```
ghost fn class_C__upcast_at (c: class_C) … requires class_C__as_P c #p m
                                           ensures class_C__inv_at (mkdyn (view (class_C__obj c))) …
```

The value changes — `c` is a box, and the upcast produces `mkdyn (…)` — where a C#
reference conversion does not. That is a property of the encoding, not of the source
program, and it is invisible to the C# semantics because the box is unreachable
afterwards: the only way back is R9.16, which requires the index.

**R9.15 is recorded by the frontend, not found by the emitter.** C# performs the
conversion silently and Roslyn already says where: at every expression whose
`ConvertedType` is a class other than its `Type`. The lowerer wraps exactly those in an
`IrConvert`, so the emitter has *one* rule applied wherever the node appears — a local
declaration, an argument, a `return` — rather than one rule per position, and a position
nobody thought of is a position that already works. `Shape s = sq;` and
`Square q = (Square) s;` are then the same IR node, told apart by the hierarchy rather
than by the syntax.

**R9.15a — The conversion also has a value form, and that is what a statement uses.**
Pulse matches resources by name, so a ghost upcast followed by `let x = mkdyn (…)` leaves
the invariant attached to the term and not to `x` (Error 228, the same fact R3.8's object
locals are already shaped by). `class_C__to_P_at` is the ghost step followed by the
reference, returning it, so the conversion is one operation:

```
let t0 = func_Square__ctor 5l;
with vs_0. assert (class_Square__inv t0 vs_0);
let vShape_1 : erased (class_Shape__model) = hide (class_Square__forget vs_0);
fold (class_Square__as_Shape t0 (reveal vShape_1));
let var_s = Vtbl_Square.class_Square__to_Shape_at t0;
```

The `with` is not a proof step but the naming R9.6 needs: the view is folded at the
forgetting of *whatever model the constructor established*, and only the prover can name
that. Currently inserted at a local declaration whose declared type is the immediate base;
the other three positions and longer chains are refused with a diagnostic rather than
emitted untested.

**R9.15b — The conversion keeps the index, and the *emitter* is what drops it.** The
`_at` form ensures `class_P__inv_at s (hide (class_C__obj_of t)) p m`, not the anonymous
`exists* o. inv_at s o p m` that R9.3's reference is. Keeping it is what makes R9.16
provable at all, and dropping it is a separate, explicit step, `class_P__forget_impl s o`,
because an indexed reference cannot be handed to a method (whose parameter is anonymous by
R9.3), stored, or returned. The emitter therefore forgets the index of

* every argument of a call except a receiver it is dispatching on,
* a returned object,
* an object local at the end of its scope (R3.8's drop, at the indexed resource).

`class_P__forget_impl` takes the object record explicitly and **leaves both its permission
and its model to inference**: naming the model with a `with` would bind an opaque witness
and sever the link to the constructor's post-state, which is F34/R4.11a again.

**R9.15c — The conversion consumes the derived reference.** C# leaves both names usable;
the encoding cannot, because the derived object's invariant *becomes* the base's. The old
name is marked cast and its next use is **PALCS0548**. Converting a name the method does
*not* own outright — its own receiver, or an object parameter — gives away an invariant
R4.10's epilogue owes back, and that is left to Pulse: the epilogue simply cannot be
proved, and R2.3 puts the refusal on the `return`, where the promise comes due
(`test/pulse_refusals/cases/UpcastParameter.cs`). It was briefly **PALCS0549** here, on the
reasoning that such a method's specification "cannot hold, whatever the emitter does". That
is false, and the check was hiding why: a conversion is not one-way, and R9.16's downcast on
a leaf proves reference identity outright (`class_C__from_B` ensures `r == reveal c`), so
`B s = d; …; D back = (D)s;` really does return the resource to the reference the parameter
names. What it does not return is the *model* — an intermediate `__from_B` promises only
`m == forget own`, and forgetting is not injective as far as F\* is concerned — so the
roundtrip fails today for a specific and fixable reason that no program could reach while
the refusal stood. What is left is
**PALCS0546**, a conversion between two classes the hierarchy does not relate at all
(R9.18c makes several levels at once ordinary). A cast *down* in expression
position stays **PALCS0547**, because unlike the upcast it also binds the model equation
the caller reasons with, and an equation needs a name.

**R9.15d — A method may return an object, and R4.12 is where that was already written.**
A constructor's postcondition owns the object it built and calls it `this`; an ordinary
method's owns the object it returns and calls it `Result`. That is the only difference, so
the rule is stated once for both: a class-typed return adds
`exists* post_result. class_P__inv var_result post_result` to the `ensures`, and `Result`
in the contract denotes *the model*, never the reference — `Result.TheArea` means something
only under that reading, and a reference is a thing no specification can say anything about.

A base-typed array is therefore heterogeneous with no extra machinery (`shape_slot` in
both studies), and `total_area` traverses one at a fraction.

**R9.15e — The forgotten model is bound to a name of the *base's* model type before the
fold.** R9.15a's `with` names the model the value is held at; that name has the *derived*
class's model type, and R9.5 gives every class its own `__model` refinement even where the
forgetting between two of them is `fun m -> m`. So `fold (… (class_C__forget vc_0))`
leaves the base reference owned at a term whose only known type is `class_C__model`, and
the base's observations — which are functions of a `class_P__model` — cannot be unfolded
on it. The fix is to say what type the forgotten model has, once, where it is produced:

```
let vP_1 : erased (class_P__model) = hide (class_C__forget vc_0);
fold (class_C__as_P c (reveal vP_1));
```

This is not a proof step and not a hint. The reference the cast produces is owned at
whatever names its model, and that name is what a caller's implicit is later instantiated
with; binding it at the base's type is the difference between handing back a `P` and
handing back a `C` that happens to be spelled like one.

*Why it was invisible for so long.* Where the forgetting does arithmetic — `Side * Side`,
`Radius * Radius * 3`, a projection out of a struct — the application is at the base's type
by construction and nothing is lost. It bites only when the forgetting is the **identity
on a bare model**, because then the term is literally the derived model and there is no
operator to retype it. `test/shape_hierarchy`'s `Tile`, whose model *is* its area, is that
case; before this rule, `SumTiles` failed to discharge `SumAreas`'s precondition — a
precondition written entirely at `Shape`, about a `Shape`, on a line where nothing about a
`Tile` is in scope. §18's reading applies: the empty cell in the shape matrix was "a leaf
that adds no information to its base", which is the *simplest* leaf there is and so the
one no test had.

*A receiver that is never cast.* R9.7's bracket presents a direct call's receiver at the
model its `override`'s contract is written at, and that is the same naming, so it takes the
same binder:

```
with vT_0. assert (class_Tile__inv var_t p vT_0);
let vShape_1 : erased (class_Shape__model) = hide (class_Tile__forget vT_0);
fold (class_Tile__as_Shape var_t p (reveal vShape_1));
```

No conversion has happened here — `t` is a `Tile` before the call and after it. It is the
*contract* that lives at the base, which is enough: the callee's precondition is stated in
`Shape`'s vocabulary and has to be discharged in it. `Shapes.DirectTile` is the case.

*The edge out of an abstract class.* R9.18's classes have no representation to view, so the
cast is one generated ghost function and there is nothing to fold: the base model cannot be
named before it is produced. It is named after, and the resource is moved onto the name:

```
let t2 = class_C__to_P_at c o;
let vP_2 : erased (class_P__model) = hide (class_C__forget (reveal vC_1));
rewrite each (class_C__forget (reveal vC_1)) as (reveal vP_2);
```

The move is the whole of it. Where the forgetting is the identity, Pulse reduces
`class_C__forget m` back to `m` and instantiates a later caller's implicit with *that*; a
binder has no further reduct, so the rewrite is what stops it. The `each` form mentions
neither the index nor the permission, so it is one step whatever the reference is held at.

*A chain is walked in pieces.* `Rect r = new Rect__impl(6);` followed by `AtMiddle(r)` is
two conversions over one value, so the name an earlier edge bound the model under travels
on the slot, exactly as R9.15b's index does. An edge whose predecessor bound no name — the
first edge out of an abstract class, whose own model was never named — binds none either
and has nothing to forget.

`test/open_class` is the case written out: a four-level chain in which the two lowest edges
both forget by the identity. It is also the hand-written desugaring of an *open* concrete
class (§9.1's `sealed` restriction), which is what makes those two edges identities — they
were not class boundaries in the program the user wrote.

### 9.7 Downcast

**R9.16 — A cast to a derived type requires the ghost index naming the object.** It is
emitted as the chain walker plus one `recover`, and it needs no assumption beyond R9.13.
The precondition *is* the knowledge, and it is the same index `gather` already forced.

The base emits two constructs for it, next to `share`/`gather`:

```
let class_P__box (o: class_P__obj) : Dn.dyn = Dn.mkdyn o.rep
fn  class_P__rep (s: class_P) (#o: erased class_P__obj) …
      requires class_P__inv_at s o p m ensures … ** pure (d == class_P__box o)
```

`rep` walks the chain — `unfold inv_at; recover; fold inv_at` — and returns the box rather
than `o.rep` itself, because reading the field needs a coercion across `o.pkg.impl ==
class_C`, which is only propositionally true. Each leaf emits the cast:

```
fn class_C__from_P (s: class_P) (#c: erased class_C) (#p: perm) (#m: erased class_P__model)
  requires class_P__inv_at s (hide (class_C__obj_of (reveal c))) p m
  returns  r: class_C
  ensures  class_C__as_P r #p m ** pure (r == reveal c)
```

and the client is R9.15b's index followed by that cast and R3.8's unfold:

```
let var_s = Vtbl_Square.class_Square__to_Shape_at t0;
let t1 = class_Shape_Double_at var_s;
with vs_1. assert (Class_Shape.class_Shape__inv_at var_s (hide (…__obj_of t0)) 1.0R vs_1);
let var_sq = Vtbl_Square.class_Square__from_Shape var_s;
unfold (Class_Square.class_Square__as_Shape var_sq vs_1);
with vsq_2. assert (Class_Square.class_Square__inv var_sq vsq_2);
```

The `pure (r == reveal c)` is what makes the round trip an identity, so a `Square` cast up
and back is the same reference. Using a name after it has been cast is **PALCS0548**: C#
would let both names live, the encoding does not, and saying so at the C# use is better
than a resource mismatch at the Pulse one.

**The cast recovers the type, never the model.** After `Shape s = new Square(5)` only the
observations R9.6's forgetting kept survive, so `GrowAndMeasureSide` can conclude
`Result * Result == 100` and not `Result == 10`. That is C#'s semantics, not a weakness of
the encoding: an upcast really does lose static knowledge, and a program that needs it back
should not have upcast.

Be precise about what this proves. `recover` has no failure mode: it is not "test the
header and maybe fail" but "given a proof the header matches, hand back the value". So the
cast cannot fail — not because anything proves a runtime test succeeds, but because the
encoding only lets a user *write* the casts whose test is redundant. A cast that might
fail is not one this scheme proves safe, it is one this scheme cannot express, and `as`,
`is` returning `false`, and a throwing cast are all refused. That is consistent with
exception-freedom (§6): a verified cast is one that cannot throw.

**R9.17 — The encoding is an implementation detail, and F* is what enforces that.**
Everything above is a *scheme*, and a scheme's choices are its own business. R9.3 makes a
reference `FStar.Dyn.dyn` and R9.16 recovers from it through an assumption; both are
decisions made for §9's convenience, and neither is anything a C# program can talk about.
So each generated class module is emitted as an interface and an implementation, and the
split is by *who is entitled to know*:

| | Class_C.fsti | Class_C.fst |
|---|---|---|
| the model type and its `spec_C_*` observations | definition | — |
| `class_C__vtbl`, `class_C__obj` | definition | — |
| `class_C : Type0` | `val` only | `= Dn.dyn` |
| `inv`, `inv_at`, `forget_impl`, share/gather, the dispatchers | signature | body |
| `class_C__at`, `class_C__box`, `class_C__rep` | — | all of it |
| `class_C__pack`, `class_C__unpack` | signature | body |

The vocabulary a specification is written in — the model and its observations — is wholly
public, because every contract about the class is stated in it. The vtable and the object
record stay transparent too, but for a different reason: they are the class's *dispatch
interface*, the thing a subclass builds, not its encoding. What becomes private is the
representation of a reference and everything that reads it.

Two new primitives are what make that possible, and they are the interface's whole content
on the subject:

```
fn class_C__pack (o: class_C__obj) (#p: perm) (#m: erased class_C__model)
  requires o.pkg.inv o.rep p m
  returns  s: class_C
  ensures  class_C__inv_at s (hide o) p m

fn class_C__unpack (v: class_C__vtbl) (x: erased v.impl) (s: class_C)
                   (#p: perm) (#m: erased class_C__model)
  requires class_C__inv_at s (hide ({ pkg = v; rep = reveal x })) p m
  returns  r: v.impl
  ensures  v.inv r p m ** pure (r == reveal x)
```

`pack` is R9.15a's ghost step with the dyn taken out of it; `unpack` is R9.16's recovery
with the dyn *and* the assumption taken out of it — its precondition says only "the index
is this vtable applied to this value", which is exactly the knowledge R9.16 already
required. `Vtbl_C` then reads:

```
fn class_Square__to_Shape_at (x: class_Square) (#p: perm) (#m: erased class_Shape__model)
  requires class_Square__as_Shape x #p m
  returns  s: class_Shape
  ensures  class_Shape__inv_at s (hide (class_Square__obj_of x)) p m
{
  rewrite (class_Square__as_Shape x #p m)
       as ((class_Square__obj_of x).pkg.inv (class_Square__obj_of x).rep p m);
  class_Shape__pack (class_Square__obj_of x) #p #m
}
```

with no `Dn.mkdyn` and no `CAs.recover` anywhere in it. The measurable consequence, and the
one worth checking for: in `test/shape_hierarchy`, `FStar.Dyn` occurs in **exactly one**
generated module out of twenty-eight. The subclass modules get interfaces on the same
principle — `obj_of` and the two casts are published, the vtable *value* that implements
them is not.

`class_C__upcast_at`, which R9.15a used to go through, is gone: its `ensures` named
`Dn.mkdyn` and so could not be stated in an interface at all. That it had to disappear is
the encapsulation working — a signature that cannot be written without the encoding is a
signature that was leaking it.

**What is *not* interfaced, and why.** A `sealed` class keeps a single `.fst`. R4.10 has
its methods `unfold` and `fold` `class_C__inv` — and those methods are *separate F\*
modules* (`Func_Square_GetArea`), so an abstract leaf invariant would need its opening and
closing published as ghost functions. That is a real rule, not a difficulty, but it is a
rule about §4 and not about §9, so it is left until there is a client that wants it.


Each of these is a construct with no image under the scheme, diagnosed at the C#
declaration that asks for it, never a prediction about a proof:

| Construct | Rule |
|---|---|
| a field on an `abstract` class | R9.2 |
| `virtual` with a body; `base.M()` | R9.3 |
| a non-`sealed` concrete class | R9.4 |
| a derived class that does not override its parent's `[Model]` | R9.6 |
| a contract on an `override` | R9.7 |
| a virtual method taking or returning a non-value | R9.9a |
| an upcast anywhere but a base-typed local | R9.15a |
| `interface`, multiple bases, generics | not probed |
| a cast *down* in expression position | PALCS0547, R9.15c |
| a use of a reference after it has been converted | PALCS0548, R9.15c |
| `as`, `is`, a cast that may fail; `Pal.Is<T>` in a contract | R9.16 |

### 9.8 Depth

Everything above is stated for a hierarchy of two levels: an `abstract` root and its
`sealed` leaves. C# hierarchies are deeper, and the class in the middle — `abstract class
Quadrilateral : Shape`, with a model of its own, a virtual method of its own and leaves of
its own — is not a staging post but a real abstraction that clients program against.

**R9.18 — An intermediate class is emitted by the *same* rules as a root, over three
primitives.** The whole of §9.3–§9.7 is written in terms of "the reference `s` denotes the
object record `o`". Name that relation and give it a maker and a reader, and every other
construct is byte-identical text at every depth:

| Primitive | Root | Intermediate `Q : P` |
|---|---|---|
| `class_C__is s o : prop` | `s == Dn.mkdyn o` | `class_P__is s (class_Q__view o)` |
| `class_C__ref o` → `s` | `Dn.mkdyn o` | `class_P__ref (class_Q__view o)` |
| `class_C__obj_at s #o` → `o` | `CAs.recover s` | `class_P__obj_at s`, then `CAs.recover pob.sub` |

`class_C__inv`, `class_C__inv_at`, `class_C__at`, `class_C__forget_impl`,
`class_C__intro_at`, `class_C__elim_at`, `class_C__pack`, `class_C__unpack`, both
dispatcher forms and share/gather are then *one* definition each, emitted unchanged for a
root and for an intermediate class. Depth is therefore not a case in the emitter: there is
one `EmitAbstract`, taking an optional parent.

Three consequences are worth stating, because each was a design decision that could have
gone the other way:

* **The dyn is made once, at the root** (R9.8). `class_Q = class_P`, so a `Quadrilateral`
  reference *is* a `Shape` reference — which is what makes the upcast a ghost step and
  matches C#, where the conversion changes no bits.
* **`sub` hangs off the object record, not off the vtable.** It holds
  `Dn.mkdyn qo` — the record one level down, vtable *applied to* its representation — so
  what a descendant recovers is a working object, not a package it would have to re-apply.
  A direct leaf of the class stores `Dn.mkdyn ()`.
* **`class_C` stays abstract in the `.fsti` at every depth** (R9.17). Transparency would
  be needed only if a client crossed between two classes' reference types, and the only
  crossings are R9.18's own casts, which live inside `Class_Q`.

**R9.18a — Each edge emits a derived vtable, and its proof obligation is discharged by
SMT.** `Q` gives `P` a package built from `Q`'s: `class_Q__as_P_pkg` keeps `impl`
definitionally equal and replaces each inherited slot by a wrapper whose contract is stated
at `P`'s model. The wrapper's obligation is exactly R9.19's re-reading — the inner slot's
contract at `Q`'s model *is* the outer one composed with `class_Q__forget` — so the view's
`pure (m == class_Q__forget own)` is all the prover needs, and no lemma is emitted.

The ownership the wrapper is written over is `class_Q__as_P qp x p m`, a predicate over a
*vtable and representation* rather than over `class_Q__inv`. That is not a stylistic
choice: `class_Q__inv` is defined through `class_Q__is`, which is defined through `P`, so
using it here would close a cycle.

**R9.18b — Each edge emits two casts, and the upcast returns the reference it was
given.** `class_Q__to_P_at`, `class_Q__to_P` and `class_Q__from_P` sit beside `Q` (there is
no vtable module for an abstract class). The upcast is `elim_at`, fold `as_P`, rewrite,
`class_P__intro_at` — it must *return `s`*, because building the result with
`class_P__pack (class_Q__view qo)` would take `Dn.mkdyn` of an erased value, which does not
extract. The downcast's postcondition is existential, `exists* own. inv_at r o p own **
pure (m == class_Q__forget own)`, because forgetting is not injective: a `Shape` model does
not determine the `Quadrilateral` it came from.

**R9.18c — A conversion across several levels is the composition of the one-edge rules.**
C# writes one conversion where the hierarchy has several edges; the emitter walks the
chain and applies R9.15 (or R9.16) once per edge, in order. `Shape s = new Square(5);` and
`Square sq = (Square) s;` are therefore ordinary, and the intermediate references are the
same ones the reader would get by writing the steps out. No rule is added for depth.

**R9.18d — A virtual call goes to the dispatcher of the receiver's *static* class; the
member keeps the name its declaring class gave it.** `q.GetArea()` on a `Quadrilateral`
must reach `Quadrilateral`'s wrapper, because a wrapper's contract and invariant are
written at its own class's model and `Shape`'s would demand an invariant the caller does
not hold. The *slot* reached is the same either way, which is why the slot's name comes
from `DeclaringClass` and is stable all the way down. Concrete methods of an abstract class
(R9.13) have bodies and no slot, so they are called directly even though the receiver is
abstractly typed — "virtual" is decided by the `abstract` declaration (R9.12a) and never by
the receiver's type.

**R9.18e — Calling an `override` at the leaf's own static type opens R9.14's view.**
R9.7 writes an override's contract at the base's model, so its receiver is owned through
`class_L__as_B` and not `class_L__inv`. A caller naming the override directly — which is
what `sq.Perimeter()` on a `Square` is — hands the receiver over the same way: `fold` the
view at `class_L__forget own` before the call, `unfold` it after. It is the same two ghost
steps R9.15 emits, for the same reason, and it is the rendering of "this reference is being
used as a `B`", not a proof step.

**R9.18f — Which forwarder a call goes to is read off the receiver's static type, not off
the class that declared the member.** R9.18 gives every class a wrapper for every method it
inherits, so a `Quadrilateral` has a `class_Quadrilateral_GetArea` even though `GetArea`
was declared on `Shape`. Choosing by the declaring class instead would hand a
`class_Quadrilateral` to a wrapper expecting a `class_Shape` — a reference of the wrong
type, in a file that translated without a single diagnostic.

The receiver's static type is exactly what C# resolves the call against, so the rule is
"translate the receiver, not the declaration". It bites only through a *synthesised*
receiver: `q.GetArea()` on a `Quadrilateral`-typed local already carries the type, but the
bare `GetArea()` inside one of `Quadrilateral`'s own non-virtual bodies has no receiver
expression to read a type from, and the enclosing class has to be supplied for it.
`Quadrilateral.TwiceArea` in `test/deep_hierarchy` is that call.

*Why the shape matrix had the cell empty.* A non-virtual method of an intermediate class
calling a virtual is already tested — `SemiPerimeter` calls `Perimeter()` — but `Perimeter`
is declared on `Quadrilateral` itself, so the declaring class and the receiver's static
type coincide and the wrong rule gives the right answer. The distinguishing case needs the
virtual to be declared *strictly above* the class whose body calls it, which is a
three-level hierarchy with a shared body in the middle.

**R9.19 — An inherited observation is re-read by composing the forgetting functions along `[Ensures("Result == @this.TheArea")]` is written once, on `Shape.GetArea`. At
`Quadrilateral` it means `spec_Shape_TheArea (class_Quadrilateral__forget m)`; at `Square`,
one more `class_Square__forget`. The spec emitter walks the base chain from the class the
model belongs to up to the class the observation was declared on, and composes. This is
R9.6 iterated, and it is what makes a base's contract mean something at every model below
it.

**R9.19a — A base's model must be strong enough to bound every subclass's
representation.** `Quadrilateral`'s model is a bounding box, not `{Area, Perimeter}`, and
`Shape.Double`'s precondition — `4 * Area` representable — bounds a square's side and a
box's sides but says *nothing* about a perimeter. So `Rectangle` cannot carry a class
invariant `2*(w+h) <= int.MaxValue`: no override of `Double` could re-establish it. The
perimeter bound belongs where the C# already puts it, as a precondition of `Perimeter()`.
That is a true statement about the program, and §0 rule 3 says the fix goes in the
annotations, never in the emitter.

### 9.9 Computed properties

**R9.20 — A computed property is its accessor, translated as the method the accessor is.**
C# has three property forms and §9 used to translate one of them. An *auto*-property is a
field with a generated accessor pair, and R3.4 already reads it as a field. A `[Spec]`
property is an observation of the model, and R3.9c already reads it as one. The third — a
property with an accessor *body*, over the representation rather than over the model — was
matched by neither, so R18.1 refused it. It is also the form most idiomatic C# uses to
expose state.

The rule is that the third form is not a new construct at all. A read-only property

```csharp
[Ensures("Result == @this.TheW + @this.TheW")]
public int Doubled => w + w;
```

translates exactly as the method the user could have written instead:

```csharp
[Ensures("Result == @this.TheW + @this.TheW")]
public int Doubled() { return w + w; }
```

One module `Func_C_Doubled`, `this` a `Box` of the representation opened by R9.7's frame,
the contract read from the *property* declaration (which is where C# permits an attribute
— an accessor may not carry one), and a body lowered by the ordinary rules. Nothing about
§9 changes: the getter is a nullary instance method, and every rule that speaks about an
instance method already speaks about it.

**R9.20a — A read `o.P` is the call `o.P()`.** In an executable position, a property read
lowers to R9.13's instance call with no arguments. The two spellings therefore produce
identical Pulse, which is what §7.2's variant detector requires of a style choice: the
variant of a class may write `Doubled()` where the original writes `Doubled`, and the
emitter may not be able to tell.

In a *specification* position `o.P` is unchanged: R3.9c reads a `[Spec]` member of the
model and nothing else. A computed property is executable code over the representation, so
a contract cannot mention it, exactly as a contract cannot mention an ordinary method.
That is not a restriction R9.20 adds; it is R3.9c, which is why the example above states
its postcondition over the `[Spec]` observation `TheW`.

**R9.20b — A `set` accessor is refused (`PALCS0591`).** A setter is a method of one
parameter that writes fields, so R9.20 would carry it over unchanged but for one thing:
C# gives the parameter the contextual name `value`, and every rule that binds a parameter
— R4.2's naming, R4.6's ghost arguments, the `@`-qualified spec vocabulary — assumes the
name is one the user wrote and can mention in a contract. `value` is a keyword in exactly
one position and an ordinary identifier everywhere else, and until §4 says which it is in
a specification, a setter has no contract that can be written down. Write the assignment
as a method.

**R9.20c — A property is refused if it is not read-only, and its accessor is not counted
twice.** A getter appears in `GetMembers()` both as the property and as `get_P`, an
`IMethodSymbol` whose `AssociatedSymbol` is the property. The accessor is the thing with a
body and the property is the thing with the attributes, so the two are collected as one
declaration named for the property. R2.1's mangling therefore produces `Func_C_P`, not
`Func_C_get_P`: C# forbids a property and a method of one name in one type, so the name
stays injective.

### 9.11 Open concrete classes

Everything above is stated of a hierarchy in the shape §9 encodes: an `abstract` root and
`sealed` leaves. Ordinary C# is not written that way. A class is concrete *and*
extensible, it has fields and a constructor, its virtual methods have bodies, and a
subclass inherits the ones it does not override.

The gap was, for four rounds of this work, described as a proof-shape risk: an encoding §9
would need and does not have. That description was wrong, and a probe settled it. The
hand-written desugaring of a genuinely-extended concrete base — a base with a field, a
non-virtual body reading it, two virtuals with bodies, and a subclass overriding one — is
*structurally identical* to `test/shape_hierarchy`, and verifies with no emitter change at
all. There was never a missing Pulse shape. There was only unwritten frontend code.

**R9.21 — A concrete class that is not `sealed` is split into an abstract half and a
generated leaf.** `class C` becomes:

* an **abstract `C`** carrying the model *type* and its `[Refine]`, the observations, and
  every method C declares — as an `abstract` declaration bearing the contract R9.7 says
  belongs there. No fields, no invariant, no abstraction function, so R9.2 holds of it.
* a **generated `sealed C__impl : C`** carrying the fields, the invariant, the abstraction
  function, the constructor, and every method body as an `override` with its contract
  stripped (R9.7 again: the contract is on the declaration the override fills).

R9.6's forgetting function on this edge is the identity: the leaf adds nothing its own
abstract half does not already know. R9.15e is what makes an identity forgetting
survivable, and it is load-bearing here — every `new C(…)` crosses this edge.

The rewrite is at the **IR level**, not the syntax level. Every IR node carries the
`IrLoc` of the syntax it came from, so a body replicated into a second leaf reports at the
one place the user wrote it. A `CSharpSyntaxRewriter` would have had to invent a position
in a file that does not exist.

**R9.21a — A constructor keeps its name and its declared return type; `ConstructsLeaf`
says what it allocates.** `new C(…)` in the user's program is untouched and really does
yield a `C`. The emitted function allocates and folds at `C__impl`, then walks R9.15's
chain once to `C` before returning. The upcast produces R9.16's *indexed* reference, and
the postcondition wants the plain invariant, so the index is dropped with one
`class_C__forget_impl` step.

**R9.21b — A subclass of an open class inherits its representation, its invariant, its
model, and every body it does not override.** R9.2 gives the abstract half no fields, so
"inherits" has to be made true by replication: what C# resolves by walking a base chain at
run time, the scheme resolves by giving each leaf the whole of what it is. Three
consequences, each forced:

* The fields are inherited at **collection** time and the invariant at **IR** time. The
  inherited abstraction function is the base's *syntax*, and it can only be lowered where
  the names it reads resolve — which is before the IR exists. The invariant is already
  lowered and refers to fields by name, so it merges safely afterwards. A semantic model
  does not span syntax trees, so an inherited model or observation body is bound against
  the model of the tree it was written in, not the subclass's.
* Flattening runs **before** splitting, base-first by depth. Inherited fields belong to the
  subclass's *leaf*, and after the split the leaf is not the class the base list names.
* **A subclass that says nothing inherits the model whole, and its forgetting function is
  the identity.** A `[Model]` member declared plainly is not overridable, so R9.6 has
  nowhere to go and there is nothing for the subclass to write. This is the default, and it
  is the right one: most subclasses add representation, not *model*. R9.21d is what happens
  when a subclass wants more.

A moved or replicated method's receiver is retyped to the leaf, because R4.10 opens it
against its own invariant and the abstract half has none. Its `Overrides` is set to the
leaf's **immediate base** — its own abstract half — because R9.14 reads `Overrides` as the
view the receiver arrives under, not as the class that first declared the slot. An
`override` *moves*: §9.9 never re-declares an inherited abstract method, and doing so here
gives the class a second vtable slot of the same name.

**R9.21c — `D(…) : base(args)` is inlined.** There is one object here, not two, and the
base's constructor builds the base's *leaf*, which `D` is not. So R4.12c's reading of
`: this(args)` — that the chained constructor is the result — is exactly what does not hold
of `base`. Instead the base's constructor parameters are bound to the arguments and its
field assignments are prepended to `D`'s own. The binding is a **renaming**, not a
substitution: nothing traverses the expressions, so nothing can get one wrong, and a
capture is harmless because `let var_b = var_b;` binds the outer `var_b`'s value. R4.12's
"a constructor body is field assignments" therefore admits a leading run of `let`s, and
nothing else.

**R9.21d — A `virtual` `[Model]` member lets a subclass extend the model, and R9.6 is
already the rule for it.** `virtual` is the C# for "a subclass may replace this". Write it
on the `[Model]` member of an open class and everything R9.6 says of an abstract base
applies unchanged: the subclass declares a `[Model]` of its own over the fields it now has,
and overrides the base's to say what the base's model *is* in terms of it. The forgetting
function is then a **projection** rather than the identity, which is what makes the subclass
a proper refinement rather than a renaming — `Rewards` knows a balance and a points count,
`Acct` knows a balance, and no function of an `Acct`'s model recovers the points.

No rule changed to allow this; one had to be stated, about **observations**. An observation
is written against the model member of the class that declares it (`TheBalance => Bal`), so
replicating it into a subclass is correct exactly while the model is that same member. Once
a class supplies a model of its own, `Bal` there is the *forgetting function*, not the
model, and copying the body down reads a member that is no longer what it was. So an
observation is inherited only when the observation and the model are declared by the same
class; otherwise it belongs to the earlier model and is reached through R9.6's forgetting,
exactly as it is from an abstract base.

The comparison is against the **model's** declaring class and not the subclass's, and the
variant is what forced that: `Pallet : Crate : Box` inherits `Crate`'s extended model whole,
so it must take `Crate`'s observations with it and leave `Box`'s behind. A guard written
against the subclass gets the two-level case right and that one wrong.

**Implemented and verified**, by `test/open_model`: `Acct → Rewards`, where `Rewards`'s
model is a user spec type (§11) carrying a component `Acct`'s cannot name, and clients prove
both halves of the claim — the extended model is exact at the type that declares it, and a
base-typed reference sees the projection, unchanged by a method that moved only the extra
component. `CrateVariant.cs` is §7.2's detector: three levels, the extension at the
*middle* one, a base model that is a computed expression rather than a field, and a third
level that adds no model of its own so that R9.21b's identity sits directly on top of
R9.6's projection.

**What this costs, and why the cost is right.** A `virtual` method's contract lives on the
abstract half, so a caller learns only that contract even when it can see the `new`. That
is not a weakness of the translation: an overridable method may be overridden in another
assembly, and C# gives a caller no more. The loss is confined to `virtual`; a non-virtual
method keeps its contract exactly, which is why `Bank.Basic` proves an equality while
`Bank.Fees` proves only a bound.

**Implemented and verified**, by `test/open_concrete`: a three-level open hierarchy
`Account → Premium → Gold` written as ordinary C#, with a field, a non-virtual body, two
virtuals with bodies, an override at each level, a method added at the deepest level, and
`: base(…)` chaining at two levels. `CellVariant.cs` is §7.2's detector — an independently
written open hierarchy whose constructors take two arguments, pass an *expression* to
`base`, and chain through the middle level — and it passes with no emitter change.

### 9.12 Status


**Implemented and verified**, by `test/shape_hierarchy`: an `abstract Shape` with two
virtual methods and an observed model, `sealed Square` and `sealed Circle` with unrelated
representations, and a client that reads through dispatch, mutates through dispatch,
dispatches inside a loop, and upcasts a fresh leaf to the base. `ShapesVariant.cs` is
§7.2's detector and passes with no emitter change.

Two failures during the build were fixed where §0 rule 3 says they belong. `RepeatArea`'s
loop re-quantifies the shape's model, so a bound its precondition established has to be
restated as a `Pal.Invariant` — an annotation in the `.cs` file. And an earlier client
whose growth was exponential was dropped, because no invariant its bound could support
existed; that is a true statement about the program, not a gap in the scheme.

`Circle` is the evidence that the translation is not fitted to `Square`: it was added after
the emitter was complete, with a different representation, a different forgetting function
and a nonlinear observation, and needed no emitter change at all.

The checked downcast R9.16 is implemented too, and verified by `Shapes.MakeAndSum` (two
upcast locals whose indices are forgotten at a call) and `Shapes.GrowAndMeasureSide` (upcast,
virtual call at the index, downcast, then a `Square`-only method) — both, again, in the
variant as well.

Building it uncovered a *pre-existing* defect that R9.15b's forgetting made visible: a
read-only object parameter's postcondition was unusable by callers, because the mutation
analysis asked `Normalize.Assigned`, whose answer is "which names need a mutable cell"
(R4.2) and which may therefore say "everything a call touches". For a model that is not a
conservative approximation but a loss: the object comes back anonymous and
`Result == a.TheArea + b.TheArea` cannot be stated. R4.11's rule now lives in exactly one
place, `Normalize.Mutated`, and is used both for a method's parameters and — this is the
same fact one level down — for deciding which of a loop's objects R5.8b may hold fixed.

The conversion now happens wherever C# performs one. `Shapes.SumFresh` converts a fresh
object and a named local at two argument positions; `Shapes.MakeShape` returns one. Both
have variants that convert at the other argument, the other class and the other position,
and needed no emitter change — which is the §7.2 detector doing its job, and is the payoff
of recording the conversion in the frontend rather than recognising it at one privileged
site.

Not yet implemented: heterogeneous arrays — an array of a base type needs R6's array rules
to carry an object invariant per element, which §6 has not probed — and the *cross-method*
downcast, where the index travels in a contract (`Pal.Is<T>`) rather than within one body.

R9.17's interfaces were then applied to the whole of the above and changed no client and no
proof: the same fourteen client methods verify against `val class_Shape : Type0` as
verified against `Dn.dyn`, which is the evidence that nothing outside `Class_Shape` was
depending on the encoding. The provenance lint now reads `.fsti` as well as `.fst`, so a
construct cannot escape §7.2's detector by being declared rather than defined.

**Depth three (R9.18/R9.19) is implemented and verified**, by `test/deep_hierarchy`:
`Shape > Circle` and `Shape > Quadrilateral > {Square, Rectangle}`, where `Quadrilateral`
is abstract, has a two-number model of its own, declares a virtual `Perimeter()` and a
concrete `SemiPerimeter()` that calls it, and inherits `GetArea`/`Double`. The client
programs at all three static types, dispatches an inherited virtual at the intermediate
class, loops, converts at both edges and in one step across both, and casts back down one
and two levels. `ShapesVariant.cs` is §7.2's detector and passes with no emitter change.

`Rectangle` is depth three's `Circle`: a second leaf of the middle class with an unrelated
representation, added after the emitter was complete, and it needed no emitter change —
only the removal of a class invariant its base's contract could not support (R9.19a).

Three defects the two-level suite could not see were fixed while building it, each in the
scheme rather than in an example: a virtual call was going to the *declaring* class's
wrapper rather than the receiver's (R9.18d); a call to an `override` at the leaf's own
static type was not opening R9.14's view (R9.18e); and a concrete method of an abstract
class was being taken for a vtable slot because the test was the name and not the
`abstract` declaration (R9.12a). A fourth was a refusal that had been stated only for the
receiver: converting *any* object parameter gives away an invariant the method's own
postcondition owes back. That was PALCS0549, and it is gone — R9.15c says why, and
`test/pulse_refusals/cases/UpcastParameter.cs` is the case.

Depth four and beyond is supported by construction — every abstract class emits `sub`, the
three primitives and, if it has a parent, a derived vtable and two casts — but is untested.

---

## 10. Recursive data structures

A `Counter` owns a number. A `Stack` owns an array. A `Range` owns two `Counter`s. In every
one of those, R3.10's invariant is a *flat* `exists*` over one record, and it is flat
because the class's field graph is finite and acyclic and known at emission time.

A `Node` with a `Node? next` is not. Its invariant has to be an **induction**, and §10 is
about what that induction is, where it comes from, and who writes it.

### 10.1 What PAL does, and what is wrong with it

PAL's answer for C (`../pal/test/recursive_struct/recursive_struct.c`) is to give up and
hand the user Pulse. The user writes

```c
_include_pulse(ListPredicates,
  "let rec is_list (head:list_node_ptr) (p:perm) (l:list int)
     : Tot slprop (decreases l) = match l with … ")
```

then hand-writes three ghost lemmas — `is_list_nil_case`, `elim_is_list_nonnull`,
`intro_is_list_cons` — and then invokes them by hand, with `_ghost_stmt(…)`, at every null
test and around every field read. The predicate, the lemmas and their placement are all the
user's problem, and all three are written in a language that is not C.

That is a reasonable escape hatch and pal-csharp keeps the equivalent one (`[PulseBody]`,
`IncludePulse`). But it is not an *annotation language* for this feature: nothing about the
predicate is specific to the proof, and nothing about the placement is specific to the
program. Both are functions of the class declaration and of the C# control flow. §10's
claim is that the user should write **no Pulse at all** — only the `[Model]` member they
already have to write for every class (R3.9), and the `if (n == null)` they already have to
write for the program to run.

### 10.2 The representation

**R10.1.** A class is **recursive** when at least one of its fields has the class's own
nullable type. Its representation, its reference type and its nullable form are emitted as
one mutually recursive group (F35):

```fstar
noeq type class_Node__raw = {
  fld_value: I32.t;
  fld_next: class_Node__opt;
}
and class_Node__opt = B.box class_Node__raw
and class_Node = b: class_Node__opt { not (B.is_null b) }
```

**R10.2.** `C?` is `B.box C__raw`, and `C` is its **non-null refinement**. A Pulse `box` is
already a nullable pointer (F76): the library gives `B.null`, `B.is_null` with
`b <==> r == null`, and `B.pts_to_not_null`. C#'s `C` and `C?` are likewise one runtime type
plus an annotation. So the honest image of the pair is one type plus a refinement, and the
subtyping `class_C <: class_C__opt` is F*'s ordinary refinement subtyping.

The null test is then `B.is_null x`, whose boolean is *definitionally* the equation
`x == B.null`, so the base case of the induction stays reachable by the prover: `pure (x ==
B.null)` on one side, `[]` on the other, and `class_C__cases` (R10.4) bridging them — the
same shape as before, with the constructor replaced by a decidable equality.

> *Why not `option class_C`? Because `Box` already has a null, and wrapping it gives two
> nullability layers rather than one. The fact a field access then has in hand is `Some? x`
> — a fact about the *encoding*. Under the refinement it is `not (B.is_null x)`, which is
> exactly the annotation the C# programmer wrote. The whole content of the `option` layer
> was the two coercions R10.2b/R10.2c now describe, and those are the identity.*

**R10.2a.** A nullable reference is *owned through the nullable type*: the resource for a
slot of type `C?` is `class_C__inv_opt x #p m`, not `class_C__inv`. R10.3a defines the
non-null invariant in terms of the nullable one, so every §3, §4 and §5 rule that mentions
`class_C__inv` keeps working with no case for recursion.

**R10.2b.** A non-null `C` used where a `C?` is expected — an argument, a `return`, the
right-hand side of a field write — is **the identity**. C# calls it an identity conversion
because nullability is an annotation rather than a type, and R10.2 makes the encoding agree:
`class_C` is a refinement of `class_C__opt`, so the term is already at the wider type. No
coercion is emitted and no lemma is needed to move the invariant, because
`class_C__inv this p m` *is* `class_C__inv_opt this p m` (R10.3a).

**R10.2c.** The converse is also the identity *text*, but not a free step: a `C?` used where
a `C` is expected obliges the solver to discharge `not (B.is_null e)`. In C# that position is
spelled with the null-forgiving operator, `f(x!)`, or is reached by flow narrowing inside an
`if (x != null)` branch. Both work, and for the same reason: the branch condition C#'s own
flow analysis used is the hypothesis F* discharges the refinement from. So `f(x)` and `f(x!)`
translate identically (R10.5 makes `!` transparent), and neither needs the emitter to read
flow analysis — the SMT context already has what the branch put there.

R10.2b and R10.2c therefore have **no emitter component at all**, in code or in
specification position: no coercion wrappers, no widening at an equality, no non-null/
nullable distinction to carry through the IR. This also disposes of a standing wrinkle.
Specification strings are bound by a shim compiled with `#nullable disable` (§4), so a type
recovered from the shim's symbols cannot distinguish `C` from `C?` — which is harmless,
because there is nothing to distinguish them *for*.

**R10.2d.** Allocation is where the refinement is *established*. `B.alloc` returns
`class_C__opt`; a constructor returns `class_C`. The bridging step is `B.pts_to_not_null`,
applied to the `pts_to` the allocation just produced, and it is emitted immediately after
every `B.alloc` (R10.6a, R12.4). This is not the emitter inventing a proof: `new` is
non-null in C#, the surface type already says so, and the step that discharges it is a Pulse
library lemma applied uniformly.

### 10.3 The invariant

**R10.3.** The invariant of a recursive class is a `let rec` over the *nullable* reference,
by cases on the **model**, with `decreases` on the model (F36):

```fstar
let rec class_Node__inv_opt ([@@@mkey] x: class_Node__opt) (p: perm) (m: class_Node__model)
  : Tot slprop (decreases m)
  = match m with
    | [] -> pure (x == B.null)
    | hd :: tl ->
      exists* (r: class_Node__raw).
        B.pts_to x #p r **
        pure (hd == I32.v r.fld_value) **
        class_Node__inv_opt r.fld_next p tl
```

Note what the cons case does *not* have. Under the option encoding it bound a second
existential `v` for the node, reachable only through `pure (x == Some v)` — precisely the
shape R16.3 identifies as one Pulse's matcher cannot solve for. R10.2 removes it at the
source, and with it the commonest instance of that problem.

Three things are load-bearing and none is a choice.

* **The recursion is on the model.** By cases on `x` there is no measure (F36).
* **`[@@@mkey]` is on the reference.** It is the key Pulse matches resources on; without it
  a goal at one model is not found in a context holding the predicate at another.
* **The permission is an explicit parameter, not meta-defaulted.** F21's `#[T.exact …]`
  default cannot be written on a `let rec` binder that the recursive call must instantiate.
  R10.3a restores the defaulted form at the top.

**R10.3a.** The non-null invariant every other rule already talks about is *derived*:

```fstar
let class_Node__inv (this: class_Node) (#[T.exact (`1.0R)] p: perm) (m: class_Node__model)
  : slprop
  = class_Node__inv_opt this p m
```

The argument is `this` and not an injection of it, because R10.2 makes the two types one.
That is what makes R10.2b free, and it is why the derived `class_C__as_opt` and
`class_C__intro` lemmas are now one `rewrite` each rather than a re-fold.

so a recursive class is an ordinary class whose invariant happens to be defined by
recursion, and R4.5's contracts, R4.10's fold/unfold window and R3.10b's nesting need no new
case.

### 10.4 Where the induction comes from — the notation

**R10.5.** The user writes no predicate. They write the `[Model]` member R3.9 already
requires, as a **structural function of the fields**:

```csharp
public sealed class Node
{
    private int value;
    private Node? next;

    [Model] private SpecList<SpecInt> Items => SpecList.Cons(value, next!.Items);
}
```

and the emitter reads it as an induction, by inverting the equation.

The `!` is required — the core invariant says annotated C# compiles unmodified, and a stock
compiler with `<Nullable>enable</Nullable>` will not accept `next.Items` — and it is also
the right reading. It is not a claim that `next` is non-null; it says the member is
**total**: a null reference denotes the empty structure, so `next!.Items` is `[]` when
`next` is null and the equation holds in both cases. That totality is exactly what lets the
equation be read backwards as an induction *with a base case*, and nothing here is ever
executed. The rule is exactly
this and nothing wider:

> The `[Model]` body of a recursive class must be a single application of a **model
> constructor** to arguments, each of which is either
>   (a) a pure expression over the class's non-recursive fields, or
>   (b) `f.M`, where `f` is a field of the class's own nullable type and `M` is the same
>       `[Model]` member.
>
> The constructor's inductive type must have exactly one other constructor, taking no
> recursive argument. That one is what a **null** reference denotes.

Two model types ship with the language, and a third is not needed to make the rule general —
the rule is stated over the constructor's arity, not over the type:

| C# spec type | Pulse | "nil" constructor | recursive constructor |
|---|---|---|---|
| `SpecList<T>` | `list ⟦T⟧` | `SpecList.Empty` | `SpecList.Cons(head, tail)` |
| `SpecTree<T>` | `Pulse.Lib.CSharp.Tree.tree ⟦T⟧` | `SpecTree.Leaf` | `SpecTree.Branch(left, value, right)` |

The derivation is then mechanical. For a model constructor `K a₁ … aₙ` where the recursive
arguments are `aᵢ = fᵢ.M` and the pure ones are `aⱼ = eⱼ`:

```
⟦class C⟧ᵢₙᵥ =
  let rec class_C__inv_opt ([@@@mkey] x) (p: perm) (m) : Tot slprop (decreases m) =
    match m with
    | <Nil>          -> pure (x == None)
    | K b₁ … bₙ      -> exists* (v: class_C) (r: class_C__raw).
                          pure (x == Some v) **
                          B.pts_to v #p r **
                          pure (⋀ⱼ bⱼ == ⟦eⱼ⟧[fields := r.fld_…]) **
                          (**ᵢ class_C__inv_opt r.fld_fᵢ p bᵢ)
```

`SpecTree.Branch(left.Contents, value, right.Contents)` gives the binary-tree predicate by
the same rule, with two recursive conjuncts instead of one (F42).

**R10.5a (refusals).** Anything the derivation does not cover is refused with a diagnostic,
never approximated:

| Diagnostic | Refused |
|---|---|
| PALCS0560 | A recursive class whose `[Model]` type is not one of the inductive spec types. |
| PALCS0561 | A `[Model]` body that is not a single constructor application (R10.5). |
| PALCS0562 | A recursive field that the `[Model]` body does not mention, or mentions other than as `f.M`. |
| PALCS0563 | A recursive class that also has an array field or a non-recursive object field — the induction and R3.10a/R3.10b's flat conjuncts have not been probed together. |
| PALCS0565 | A recursive class in a hierarchy (§9). The two encodings have not been probed together. |
| PALCS0566 | A `[Backward]` field (R10.10): the Pulse shape is pinned, the surface rule is not. |
| PALCS0567 | A field of a recursive class reached outside a null-test window (R10.7c). |
| PALCS0568 | A self-recursive method with no `[Decreases]` (R10.6). |
| PALCS0569 | A null test that is not the whole condition of an `if` (R10.7). |
| PALCS0579 | A cycle in the call graph — mutual recursion between methods or between `[Spec]` functions (R10.6). |

This is a narrow language. It is narrow *honestly*: every shape inside it is pinned by
`test/pulse_facts/RecursiveFacts.fst`, and §0 rule 3 forbids widening it by guessing.

### 10.5 The derived lemmas

**R10.4.** Six ghost lemmas are emitted beside the predicate, and they are what a client
uses; no client ever unfolds the predicate. This is what makes R9.17's `.fsti` treatment
apply here unchanged, and it is the whole of the improvement over PAL's `_include_pulse`.

| Lemma | Meaning |
|---|---|
| `class_C__cases x` | preserves the invariant; `not (B.is_null x) <==> <the model is a K>`. The bridge between the C# null test and the induction. |
| `class_C__nil_case x` | preserves; `B.is_null x` implies the model is `<Nil>`. |
| `class_C__elim_nil x` | **consumes**; `B.is_null x` implies the model is `<Nil>`. |
| `class_C__intro_nil x p` | `B.is_null x` gives the invariant at `<Nil>`. |
| `class_C__elim_cons x` | on `x: class_C` — R10.2's refinement type *is* "known non-null", so this needs no extra binder and no `pure` — gives up the head cell and each sub-invariant, with the model equation. |
| `class_C__intro_cons x` | its inverse. |

The forward halves of `cases` and `nil_case` are where the one cost of R10.2 is paid. Under
the option encoding `Some? x` held definitionally; under the box encoding non-nullness must
be recovered from the `pts_to`, by **`B.pts_to_not_null`**. That is a Pulse library lemma
applied at a fixed place, so it is a step, not a special case.

Two more are derived from `intro_cons`, and R10.2 has reduced both to a single `rewrite`:

| Lemma | Meaning |
|---|---|
| `class_C__intro x` | `intro_cons` at the **non-null** form: a constructor's result is a `C`, and its postcondition owes `class_C__inv`. Since R10.3a defines `class_C__inv this` as `class_C__inv_opt this`, this is now `intro_cons` plus one rewrite through that definition. |
| `class_C__as_opt x` | R10.2b used to be an injection; it is now the identity, so this lemma survives only because `class_C__inv` is an ordinary `let` that Pulse's matcher does not see through (F77). It is one `rewrite`. |

`nil_case` and `elim_nil` differ only in whether the invariant survives. Which one the
emitter uses at a null test is read off the *contract* — whether the postcondition still
owes that reference's invariant — exactly as R4.10 already reads it. A method that consumes
its argument (R10.6b's `Append` moves `x` into its result) needs the consuming form; one
that preserves it needs the other.

**R10.4d.** R3.10d's `share` and `gather` become `ghost fn rec`, recursing on the model and
proved from the class's own case lemmas rather than by `unfold` (F40). Nothing else about
R3.10c/d changes, so `[Frac]` and read-only aliasing work over a recursive structure.

### 10.6 Methods

**R10.6.** A method over a recursive class is an ordinary method (§4) with two additions.

*Recursion.* A C# method that calls itself is emitted `fn rec` and **must** carry
`[Decreases]`, whose argument is a model. `decreases` on an erased model binder is accepted,
and the obligation at the recursive call is discharged from the equation `elim_cons` hands
back (F38). A recursive method with no `[Decreases]` is PALCS0568 — inferring one would be
the emitter inventing a proof step (§0 rule 3), and is the same refusal R5.9 already makes
for a `while`. There is not even a counted-`for` case to fall back on: a recursion's measure
is a term over the model, so the only two answers are the user's and a refusal.

*Mutual recursion is refused* (**PALCS0579**). `fn rec` is a single-binding form, so a
cycle through two or more methods has no emission at all — nor does one through two
`[Spec]` functions, whose `let rec` is likewise per-definition. PALCS0568 sees only a
direct self-call, so a cycle used to reach F* intact and be rejected there by an
*internal error* ("Impossible: cycle detected after cycle detection has passed"), with no
line, no C# name, and nothing a user could act on. §0's sentinel property says the
pipeline never fails in a way it cannot explain, so the whole-program call graph — methods
and `[Spec]` functions together — is checked for cycles in the Check pass, and a cycle is
reported once, against its first member, naming the whole path.

**R10.7 (the window).** `if (n == null) … else …` **is** the case analysis, so it is where
the lemmas go — the user invokes nothing:

```
⟦if (n == null) S₁ else S₂⟧ =
  class_C__cases n;
  if (None? var_n) {
    class_C__nil_case var_n;      // or elim_nil, per the contract
    ⟦S₁⟧
  } else {
    class_C__elim_cons var_n;
    ⟦S₂⟧
    class_C__intro_cons var_n;    // at the end of the branch, as R4.10 closes its window
  }
```

`class_C__cases` comes first and unconditionally: it is what tells the prover that the two
case analyses — on the reference, which the program does, and on the model, which the
predicate does — agree. Inside the `else` branch every field of `n` is accessible by R3.11's
ordinary rules, reached through `var_n` itself, and every field *write* by R3.12's (F39).

The tests `n == null`, `n != null`, `null == n` and `null != n` all lower to the same
`B.is_null var_n`, with the branches exchanged where C# exchanges them. A null test that is not
the condition of an `if` — inside a `&&`, or assigned to a `bool` — is PALCS0569: the window
it would open has no branch to be the extent of.

**R10.7a.** Inside the window the slot's binder stays `var_n` and `elim_cons` adds a
`B.pts_to var_n`; the non-nullness the branch established is a hypothesis, so R10.2's
refinement is discharged wherever a `C` is expected. That is why `return n` and
`Append(n.next, y)` inside the branch still produce the reference unchanged, with no
re-binding, no projection and no injection.

**R10.7b.** Branch-local mutation has to be written in **tail position**. Two arms that
leave the object in *different* states — one subtree replaced, the other not — cannot be
joined by a statement-position `if`, which has to leave a single state; and each arm has its
own window to close at the state it actually reached. `else if (…) { …; return t; }` is the
ordinary C# for that, and it is a fact about Pulse's `if`, not a restriction §10 adds.

**R10.6a (allocation).** `new Node(v, n)` is R4.12's constructor, unchanged: the argument's
invariant transfers into the field by R3.10b, and R10.4's `intro_cons` is R3.10b's closing
`fold`.

**R10.6b (destructive traversal).** `x.next = Append(x.next, y)` is an ordinary R3.12 field
write inside R10.6's window. This is the case a flat invariant cannot express and the reason
§10 exists.

**R10.7c.** A recursive class's fields are reachable **from outside the class**, which
R3.11 does not otherwise allow (PALCS0523). The licence is exactly R10.7's window: the
client's own null test is what runs `elim_cons`, and `elim_cons` hands back the head cell,
so inside the branch the field is as available to a static method as it is to a method of
the class. Outside any window it is not, and that is PALCS0567. This is why a traversal like
`Lists.Length(Node? n)` can be written as a free function over `n.next` at all, and it is
what keeps the recursive class free of a method per traversal.

### 10.7 Handle classes

**R10.8.** A class holding a recursive class as a field is an *ordinary* M2 class. R3.10b
applies verbatim; only the name of the contributed predicate changes, from `class_C__inv`
to `class_C__inv_opt` (F41). So

```csharp
public sealed class LinkedList
{
    private Node? head;
    [Model] private SpecList<SpecInt> Items => head!.Elements;

    [Ensures("@this.Elements == SpecList.Cons(v, Old(@this.Elements))")]
    public void Push(int v) { head = new Node(v, head); }
}
```

needs no rule of its own, and §10 stays confined to the recursive class itself. `Push` is
three rules already written: the field read hands the sub-invariant to the constructor,
R4.12b transfers it, and R10.2b injects the result back into the nullable field.

**R10.8a.** A `preserves` method of a handle class holds only a *share* of its receiver
(R4.11 makes the receiver's permission a parameter), so the sub-invariant it can hand to a
traversal is at that permission too. A traversal such a method calls must therefore be
`[Frac]` — R4.9's ordinary annotation, discharged over a recursive invariant by R10.7's
recursive `share`/`gather`. Nothing is special-cased: a full-permission traversal is simply
a function the owner cannot call, and the message says which permission was wanted.

### 10.8 Back pointers

**R10.10.** A `prev` field breaks the rule §10 rests on. `next` is *owned* — the cell it
points at belongs to this list and to nothing else — but `prev` points at a cell that
already belongs to the list, so owning it would be owning it twice. The predicate cannot be
a function of the fields alone.

The surface answer is one attribute:

```csharp
public sealed class DNode
{
    private int value;
    [Backward] private DNode? prev;
    private DNode? next;

    [Model] private SpecList<SpecInt> Items => SpecList.Cons(value, next.Items);
}
```

`[Backward]` means: **this field is not owned.** It contributes one *index* to the class's
invariant and one pure equation to each node (F43):

```fstar
let rec class_DNode__inv_opt (left: class_DNode__opt) ([@@@mkey] x: class_DNode__opt)
    (p: perm) (m: class_DNode__model)
  : Tot slprop (decreases m)
  = match m with
    | [] -> pure (x == None)
    | hd :: tl ->
      exists* (v: class_DNode) (r: class_DNode__raw).
        pure (x == Some v) **
        B.pts_to v #p r **
        pure (hd == I32.v r.fld_value /\ r.fld_prev == left) **
        class_DNode__inv_opt x r.fld_next p tl
```

Note the recursive call: the current reference becomes the successor's index. Three
consequences, all mechanical:

* Every method over the class gains one **erased implicit** for the index. It is solved by
  unification at every call site including the recursive one, so the user writes nothing.
* `intro_cons` reads the index **off the field** rather than taking it as an argument. That
  is what makes `head.prev = n` a legal proof step: after the write, re-introducing the node
  yields the invariant at the new predecessor with no extra obligation.
* The `[Model]` member does not mention the `[Backward]` field, and R10.5's derivation does
  not look for it. `[Backward]` is what excuses it from PALCS0562.

**`[Backward]` is refused (PALCS0566).** The Pulse shape above is pinned — `RecursiveFacts.fst`
§8 verifies a doubly linked list with `Length` and a `PushFront` that writes the old head's
back pointer — but the *surface* rule is not. A freshly allocated node's predecessor index
has to come from somewhere, and no rule over C# yet says where; §0 rule 3 forbids the
emitter from inventing one, and it forbids inventing a refusal just as firmly, so the
refusal is written down as a rule with its reason rather than left as an approximation.

`[Backward]` is also one more knob, and knobs run out: it makes a *whole* doubly linked
list expressible and a list *segment* no more expressible than before. §12 is the answer to
the general case, and a doubly linked list is delivered there — with the predicate written
by the user rather than derived, which is what a back pointer needed all along.

### 10.9 Status

Pinned end to end by `test/pulse_facts/RecursiveFacts.fst`, in the emitter's own idiom and
before any rule above was written: the singly linked list with `Length`, `Cons` and a
destructive `Append`; recursive `share`/`gather`; the `LinkedList` handle class; the binary
tree with `Size` and an in-place BST `Insert`; and the doubly linked list with `Length` and
a `PushFront` that writes the old head's back pointer.

Delivered end to end from C#: `test/linked_list` (`Node`, `Lists.Length`/`Cons`/`Append`,
the `LinkedList` handle class, and §7.2's `ListsVariant` written at the opposite null-test
polarity) and `test/binary_tree` (`TreeNode`, `Trees.Size`, a functionally correct in-place
BST `Insert`, and §7.2's `TreesVariant`). Both variants verify with no emitter change, which
is what says R10.7's window is a rule about a null test rather than about how the acceptance
test happens to be phrased.

Not covered by the **derived** invariant, and refused rather than approximated: back
pointers (PALCS0566), recursion crossing a hierarchy (PALCS0565), a recursive class that
also owns an array (PALCS0563), *iterative* traversal, and mutual recursion between two
classes.

Two of those refusals are about §10's derivation, not about the language. §12 answers the
back-pointer one by handing the predicate to the user, and §16 answers the iterative one: a
segment predicate **is** the magic wand a traversal needs to give the tail back, and a
traversal written against one needs no rule §5 does not already have. What still has only
R10.7's window is the invariant §10 derives for you.

---

## 11. User-defined specification types

### 11.1 The problem

§10 reads a recursive class's ownership predicate off its `[Model]` member. To do that it
has to know two things about the model's type: what its **empty** constructor is, and what
its **non-empty** one is. Up to here it knew them by *name*: an enum with two cases, `List`
and `Tree`, chosen by matching the C# type against `SpecList<T>` or `SpecTree<T>`, both of
which the compiler recognises as primitives.

That is a bound on the language that has nothing to do with the language. A user whose
model is an association list, a rose tree, a finite map, or anything else has no way to say
so except by patching the compiler — and §0 rule 3 says a proof that needs help gets it
from the user's annotations or from the reusable library, never from a special case in the
translator. A *model type* the translator has to be taught about is exactly such a special
case, and it is one the user cannot reach.

The fix is not to add more primitives. It is to notice, per F44 and F45, that the emitter
never needed a model type at all — only a constructor name and an arity, which the user can
declare.

### 11.2 What a user declares

**R11.1.** A **user-defined specification type** is a C# type carrying `[SpecType(t)]`,
where `t` is the F\* type it denotes. Its type parameters become the F\* type's arguments,
in order. It is a specification-only type in the sense of §8: naming one in a program
method's signature is PALCS0500, exactly as for `Seq<T>`.

```csharp
[SpecType("MyPulse.assoc")]
public readonly struct SpecAssoc<K, V> { … }
```

**R11.2.** A member carrying `[SpecOp(f)]` denotes the F\* term `f`, applied to the
receiver — if it has one — followed by its arguments, left to right. That is one rule for
four C# shapes, because all four are applications:

| C# | Emits |
|---|---|
| `[SpecOp("m.f")] public SpecInt P => …` (property) | `(m.f recv)` |
| `[SpecOp("m.f")] public SpecInt M(A a) => …` (instance method) | `(m.f recv a)` |
| `[SpecOp("m.f")] public static X F(A a, B b) => …` | `(m.f a b)` |
| `[SpecOp("m.C?")] public bool IsC => …` | `(m.C? recv)` |

A discriminator needs no rule of its own: `Cons?` is a prefix function of one argument
(F44), so it is a `[SpecOp]` like any other.

**R11.3.** A static method carrying `[SpecCtor(c)]` denotes the **constructor** `c` of the
type it returns. Constructors are `[SpecOp]`s that are also *declarations*: they are what
§10 inverts, so they are marked separately and carry the extra bit that says which one is
empty.

```csharp
[SpecCtor("MyPulse.Empty", Empty = true)]
public static SpecAssoc<K, V> Nil<K, V>() => throw …;

[SpecCtor("MyPulse.Entry")]
public static SpecAssoc<K, V> Entry<K, V>(K key, V value, SpecAssoc<K, V> rest) => throw …;
```

**R11.1a.** A *specification-type declaration* — a type carrying `[SpecType]`, **or** a
type declaring any `[SpecOp]` or `[SpecCtor]` member — is skipped wholesale by the
frontend, along with every member of it.

This is not an optimisation, it is what lets a user write a specification type in an
ordinary source file beside the code that uses it. Such a declaration is not a program and
cannot survive being read as one: its members have no bodies (each says what it means in
F\* and throws), their signatures mention specification-only types in executable position,
and they carry open type parameters that no translated method may have. Without R11.1a the
first thing a user sees on declaring a spec type is a storm of PALCS0001 and PALCS0500
about code they never asked to have translated.

**R11.1b.** The placement of the three attributes is checked in its own pass, *before*
R11.1a makes the declaration invisible. The pass has to be separate for exactly that
reason: nothing downstream ever sees a spec-type declaration, so an attribute in the wrong
place would otherwise be silently ignored, and the first symptom would be PALCS0573 at some
distant *use* — a message pointing away from the mistake. It reports:

* PALCS0570 — `[SpecType]` on a type that also carries `[Model]` or `[Invariant]`;
* PALCS0571 — `[SpecCtor]` that is not a static method returning a `[SpecType]`, or
  `[SpecOp]` on a member of a type that is neither a `[SpecType]` nor the class declaring
  that type's constructors.

**R11.4.** The F\* side is the user's. It reaches the generated modules by
`[assembly: IncludePulse]` (§7), or by already being on the include path — the translator
emits the name it was given and does not check that it exists, because that is F\*'s job
and F\* does it better. A misspelling is a type error in the generated module with the C#
attribute's text in it, which is where it can be read.

### 11.3 What the compiler stops knowing

**R11.5.** `RecursiveShape` is deleted. In its place a recursive class carries a
**model shape** — three strings and an arity, all of them read off `[SpecCtor]`:

| Field | Meaning | For `SpecList<T>` | For `SpecAssoc<K,V>` |
|---|---|---|---|
| `Empty` | the empty constructor, as a term and as a pattern | `Nil` | `MyPulse.Empty` |
| `Cons` | the non-empty constructor | `Cons` | `MyPulse.Entry` |
| `ConsTest` | its discriminator | `Cons?` | `MyPulse.Entry?` |

`ConsTest` is derived, not declared: it is `Cons` with `?` appended, which is F\*'s rule and
not ours. Everything §10 emits — `NilPattern`, `NilTerm`, `ConsPattern`, `ConsTerm`,
`ConsTest` — becomes a function of this record, and the emitter's two-way branch on an enum
disappears.

F44 is what makes the `SpecList` column say `Nil` and `Cons` rather than `[]` and `::`.
Writing the *prefix* form everywhere is what lets one template serve both, and it costs
nothing: F\* prints either.

**R11.6.** A model shape's `Cons` may have **any** arity ≥ 1, with any mixture of pure and
recursive arguments, subject to R10.5's existing rule that each recursive field appears
exactly once. F45 pins the case that neither built-in shape can express — two pure
arguments and one recursive one — and it needs no new proof step: the non-empty case of the
invariant gets one `pure` equation per pure argument and one recursive conjunct per
recursive argument, which is what the template already said.

**R11.7.** `SpecTree<T>` stops being a primitive and is **re-declared in the annotation
library** using R11.1–R11.3, pointing at `Pulse.Lib.CSharp.Tree`. It keeps its name, its
members and its behaviour; what changes is that nothing in the compiler mentions it. This
is the test of the mechanism: if a type the compiler used to special-case can be expressed
without the special case, and `test/binary_tree` verifies unchanged, then the mechanism is
at least as expressive as what it replaces.

`SpecList<T>` **stays built-in**, and deliberately. It is F\*'s `list`, whose theory is in
`FStar.List.Tot` and whose operations the translator already maps; a user's first model
type should not require them to write an F\* module. The point of R11.5 is that this is now
a *convenience* rather than a *limit* — the built-in path and the attribute path produce the
same `IrModelShape`, and there is exactly one downstream mechanism.

### 11.4 Rejections

| Id | Refused |
|---|---|
| PALCS0570 | `[SpecType]` on a type that also has a `[Model]`, or is otherwise a translated class. A specification type has no representation. |
| PALCS0571 | A `[SpecCtor]` on a method whose return type is not a `[SpecType]`, or a `[SpecOp]` on a member of a type that is not one. |
| PALCS0572 | A `[SpecType]` used as a recursive class's model with no `[SpecCtor(Empty = true)]`, or with more than one. A null reference has to denote exactly one thing. |
| PALCS0573 | A member of a `[SpecType]` used in a specification without `[SpecOp]` or `[SpecCtor]`. The translator will not guess an F\* name from a C# one — that is the mistake §0 rule 3 is about, and a silently wrong name is worse than a refusal. |

PALCS0573 is the load-bearing one. It is what makes the mechanism *total*: every member of
a user's specification type either declares what it means in F\*, or is refused. There is no
path by which a member is translated to something the user did not write down.

### 11.5 Status

Pinned by `test/pulse_facts/UserSpecFacts.fst` before any of the above was written: the
prefix-constructor facts, a user-declared inductive with a two-pure/one-recursive
constructor, its inductive invariant, its eight lemmas, a recursive traversal and a
destructive traversal that writes a field inside the window.

Delivered end to end from C#: `test/user_spec_type`, whose model type is declared entirely
in the user's own file — an F\* inductive supplied through `[assembly: IncludePulse]` and a
C# surface over it carrying `[SpecType]`, `[SpecCtor]` and `[SpecOp]` — and consumed by a
recursive class the compiler translates with no knowledge of either. `SpecTree<T>` is
re-declared through the same mechanism, and `test/binary_tree` verifies unchanged.

The §7.2 detectors both apply. `test/user_spec_type/AssocsVariant.cs` is an equivalent
program written with every null test at the opposite polarity, the empty case in the
`else`, the model operations reached as instance members where the original reached them
as statics and the reverse, results bound to locals before being returned, and the key
comparison written the other way round; it verifies with no emitter change. Four
diagnostics cases cover PALCS0570–0573.

What is *not* delivered: a user cannot yet declare a spec type whose recursive constructor
has more than one recursive argument in a *class* (§10's window opens one sub-object), and
the iterative traversal of §10.7 is still refused. Neither is a limit of §11 — both are
§10's, and §11 does not make them worse. §16 discharges the second for a §12 predicate,
using a §11 spec type (`SpecFrame<T>`) to name the spine it walks.

---

## 12. User-defined ownership predicates

### 12.1 The problem

§10 derives a class's ownership predicate from its `[Model]`: one downward fold over one
recursive field. §11 lets the *model type* be the user's. Neither lets the **predicate** be
the user's, and there are structures for which no derivation can produce it.

The driving example is a **doubly linked list segment**. A segment breaks §10 three ways,
and the three are independent:

1. It is bounded at **both** ends. It carries boundary parameters — where the segment stops,
   and which node is its last — that no fold over the class's fields could produce, because
   they are not properties of the data at all: they are chosen by whoever states the
   specification.
2. Its empty case is `from == to`, a **relation between two parameters**, not `x == None`, a
   property of one. So a C# `if (x == null)` means something strictly weaker than §10
   assumes as soon as segments are in play — R10.7's case lemma is sound only when the right
   boundary is `null`, that is only for a whole list.
3. Its central lemma — that two adjacent segments compose — is a statement about **two
   instances of the predicate at once**, proved by induction. No amount of reading a
   `[Model]` backwards produces it.

And the `prev` field breaks the ownership discipline outright, for the reason R10.10 gives:
`next` is owned, `prev` points at a cell the node before it already owns. The standard
answer is that a back pointer is **constrained, not owned** — a `pure` equation the
predicate carries — and a predicate the compiler derives can only own what it folds over.

So §12 is the third and last link in a chain: §7 brings your own *module*, §11 brings your
own *model type*, §12 brings your own *ownership predicate*. It is the direct analogue of
PAL's `_plain` + `_include_pulse` + `_refine_value` + `_ghost_stmt`
(`pal/test/recursive_struct/recursive_struct.c`), and it exists for the same reason: the
general case has to be reachable without patching the compiler.

### 12.2 `[Plain]`: a class the translator derives nothing about

**R12.1.** A class carrying `[Plain]` is translated to its **representation and nothing
else**:

```fstar
noeq type class_DNode__raw = {
  fld_value: I32.t;
  fld_prev: class_DNode__opt;
  fld_next: class_DNode__opt;
}
and class_DNode = B.box class_DNode__raw
and class_DNode__opt = option class_DNode
```

That is the whole module. No `[Model]`, no `__inv`, no `intro_nil`/`elim_cons`/`cases`, no
`__as_opt`, no constructor. Everything §10 would have derived becomes the user's
obligation, which is the trade: the compiler gives up saying anything, and in exchange the
user may say anything.

Consequently, and mechanically:

* A `[Plain]` parameter contributes a **binder and no resource** to a contract. Nothing is
  owned by virtue of a reference's type; ownership is only ever what a clause says.
* `null` on a plain class is `B.null`, with **no `intro_nil`** — there is no derived
  predicate for a lemma to be about (R12.2).
* A non-null reference used where a nullable one is expected is the reference itself, by
  R10.2's subtyping, with **no `__as_opt`** — there is no invariant to re-read.
* A method returning a plain class returns a **bare reference**: no existentially quantified
  result model, no `__inv` conjunct. `Result` denotes the reference itself.

Two refusals, both about combining `[Plain]` with something that presupposes a derivation:

* **PALCS0574** — `[Plain]` together with `[Model]`. They are two answers to one question.
* **PALCS0575** — a `[Plain]` class in a hierarchy. A bare record behind a box has no vtable
  and no invariant, so there is nothing for a base class's encoding to compose with.

### 12.3 `SlProp` clauses, plain windows, plain fields

**R12.2.** A `[SpecOp]` whose C# return type is `SlProp` is an **ownership** clause. Where
it appears in a `[Requires]`, `[Ensures]` or `[Preserves]` it joins the separating
conjunction rather than the `pure`:

```csharp
[SpecOp("DllSeg.seg")]
public static SlProp Seg(DNode? from, DNode? prev, DNode? to, DNode? last,
                         SpecList<SpecInt> values) => throw new InvalidOperationException();
```

```csharp
[Requires("Dll.Seg(from, prev, null, last, xs)")]
[Ensures("Dll.Seg(from, prev, null, last, xs)")]
```

becomes `requires (DllSeg.seg var_from var_prev None var_last (reveal var_xs)) ** …`. The
decision is made purely by the C# return type, and it is the only new thing a contract can
say. Note the idiom on the Pulse side: the named wrapper is `unfold`, so slprop matching —
which is syntactic — still sees the underlying `dll_seg` and every lemma written about it
applies to a contract written in terms of the wrapper.

**R12.3.** Inside a method body, three rules, each the corresponding §10 rule with the
proof steps deleted:

| C# | Pulse |
|---|---|
| `x == null` / `x != null` in value position | `None? x` / `Some? x` |
| `if (x == null) A else B` | `if (None? x) { A } else { B }` — **no `cases`, no `elim_cons`, no `intro_cons`**; the `else` branch knows only that `x` is `Some`, which is what makes `x.f` mean something there |
| `x.f`, `x.f = e` | the same box read and box write as R3.8, reached through a value slot |

Whether a field read or write inside the window is *owned* is the user's predicate's
business, and a missing `pts_to` is a failure in their annotations. That is §0 rule 3 read
in the intended direction: the emitter neither invents the proof step nor invents the
refusal.

The `prev` write is where this pays off. Because the user's predicate only ever
**constrained** `prev` with a `pure` equation, overwriting it costs nothing: re-closing the
segment simply reports what the field now holds. A derived predicate could not have offered
this, because it would have had to own the field it folded over.

**R12.3b (a plain reference the body assigns is a cell).** R5.2 gives every assigned local a
`let mut`, and a local that happens to hold a class reference is not an exception. Its slot
is a cell and its resource is an ordinary `R.pts_to`; a field read through it reads the cell
first and projects the box out of what was read. This is what a *cursor* is — a reference
the loop moves — and it needs no rule of its own, only the ordinary one not being skipped
because the local holds a reference.

**R12.3c (a plain class's null test is an ordinary comparison).** R10.7 confines a null test
to the whole condition of an `if` because that `if` is the *extent of a window* — the region
in which §10's case lemmas have been applied. A `[Plain]` class has no derived invariant and
so no window: §12 gave the ownership of the record to the user's predicate, and whether it
is held at a given point is that predicate's business. So PALCS0569 and PALCS0567 both step
aside for a plain class, the projection is emitted, and Pulse checks the `Some?` refinement
against whatever the user's annotations establish — a loop guard, a `[Lemma]` call, an `if`.

Keeping the restriction would have been the emitter inventing a **refusal** (§0 rule 3, read
in its second direction). A cursor's null test is a *loop condition*; no window can be the
extent of a loop condition, so the rule would have ruled out every iterative traversal on
the strength of a constraint whose reason does not apply.

**R12.4.** `new C { f = e, … }` on a plain class allocates: the record is built exactly as
R3.5 builds a struct's, then boxed with `B.alloc`. **Object-initializer syntax only** — a
constructor call is refused with a diagnostic, because a constructor has a *body*, and
reading a body to learn which parameter lands in which field is precisely the deriving §12
does not do. The initializer says it outright.

The allocation is emitted **at the local's own binder**, not at a fresh one it is then
copied from: Pulse matches resources by name, so a copy would leave the context holding
`pts_to t0 _` while every later mention asked for `pts_to var_node _`. This is the same
reason R3.8's alias case shares a slot rather than rebinding one.

### 12.4 What the user supplies

Everything §10 would have derived, written in Pulse through `[assembly: IncludePulseFile]`
(R12.6) and named from C# through `[SpecOp]`, and applied in bodies through `[Lemma]` calls
(R12.7). For the doubly linked list that is the predicate

```fstar
let rec dll_seg (p: perm) ([@@@mkey] from) (prev) (to_) (last) (l: list int)
  : Tot slprop (decreases l)
  = match l with
    | [] -> pure (from == to_ /\ prev == last)
    | hd :: tl ->
      exists* v r.
        pure (from == Some v) ** B.pts_to v #p r **
        pure (hd == I32.v r.fld_value /\ r.fld_prev == prev) **
        dll_seg p r.fld_next from to_ last tl
```

and eight lemmas: `intro_nil`, `elim_nil`, `some`, `elim_cons`, `intro_cons`, `append`,
`snoc` and `cases`. Three of them are worth naming:

* **`append`** — two adjacent segments make one, by induction on the first. This is the
  lemma no `[Model]` could produce.
* **`snoc`** — extending a segment on the right, which is the step an *iterative* traversal
  takes when it advances its cursor. It is what §10.7's refused iterative traversal was
  missing, and §12 is where it can be written.
* **`cases`** — the `if (x == null)` connection, valid *only* when the right boundary is
  `None`. §12 refuses to derive it and makes the user state and prove it, which is the whole
  of point 2 above made concrete.

Three shapes recur in the lemma statements and are worth pinning, because getting them
wrong produces failures that look like unrelated problems:

* An `ensures` cannot mention `L.hd l` — `Cons? l` is not in scope there. Existentially
  quantify the tail and state `pure (l == I32.v r.fld_value :: tl)`, which is the idiom the
  emitter already uses.
* A binder introduced by `with r.` is **ghost** and cannot feed a stateful call or a box
  write. The node has to be *read* (`let node = B.op_Bang from`), which is exactly what the
  emitter does anyway (R3.8).
* `elim_cons` should state its `pts_to` **at the cursor the caller passed**, so that the C#
  body can read a field of a *program* pointer. Under R10.2 that is automatic: the cursor is
  the pointer. (Before R10.2 it needed a refined binder `(from: …__opt { Some? from })` and
  a `rewrite each v as (Some?.v from)`, plus a separate preserving lemma to establish
  `Some? from` in the first place — all three are gone.)

### 12.5 The C# face of a user predicate

§12.4 as first delivered had two blemishes. The predicate and its lemmas were a ~190-line
string literal inside an attribute argument, so no editor gave them syntax highlighting,
type checking, or a jump-to-definition; and every proof step in a body was a raw
`Pal.GhostStmt("…")`, so the caller repeated the callee's binder names, `rewrite`s and
`with`s in a language the C# compiler cannot see. Both are fixed by giving the predicate a
C# *face*, and the fix is a style rule as much as it is two translation rules.

**R12.6.** `[assembly: IncludePulseFile("path")]` is `[assembly: IncludePulse]` (§2) with
the text read from a file beside the annotated source rather than written inline. The path is
resolved relative to the file carrying the attribute; the module name is the file's base
name, and a `module` header inside the file that disagrees with it is an error (PALCS0584),
as is a file that cannot be read (PALCS0583). The emitted module is byte-for-byte the file's
contents, exactly as `IncludePulse` emits the literal's. Nothing else changes: a `.fst` in the source
tree is an ordinary F* file, so `fstar.fst.config.json`, IDE mode and `--cache_checked_modules`
all work on it with no special arrangement.

**R12.7.** A `[Lemma]` whose contract mentions **any** `SlProp` clause is emitted as a Pulse
`ghost fn` rather than an F* `Lemma`: the `SlProp` clauses become the resource conjuncts,
joined with `**`, and the remaining pure clauses are collected into a single trailing
`pure (…)`. A `[Lemma]` with no `SlProp` clause is emitted exactly as before, byte for byte.
The call site needs nothing new — R5.11 already emits a lemma application as `Module.name
args;`, which is also how a Pulse `ghost fn` is called. Ghost parameters are declared
`Ghost<T>` and erase to the underlying type, as everywhere else.

Together these turn a proof step into a C# call:

```csharp
DllProof.Open(from, from!, prev, null, last, xs);
int rest = Length(from.next, from, last);
DllProof.Close(from, from!, prev, null, last, xs);
```

**R12.7b (a `ghost fn` lemma's postcondition is read under its precondition).** R4.8 already
says this of a method: a Pulse `ensures` is type-checked with the `requires` *not* in scope,
so a postcondition that mentions `l[i]` is ill-typed until `i < l.Length` is restated as a
hypothesis. A `ghost fn` is a Pulse function, so it needs the same treatment, and a
`[Lemma]` that owns anything is a `ghost fn`. The pure-`Lemma` form is untouched: there the
`requires` *is* in scope, and restating it would only slow the SMT query down.

**The style rule.** *A user predicate publishes one ghost lemma per step a C# body takes,
whose signature mentions only what C# can name — parameters, locals, `null`, spec lists — and
keeps every `with` and every `rewrite` inside the `.fst` file.* The obstacle this navigates
is real and is worth recording, because it is what R12.4's advice about refined binders runs
into. A predicate's cons case is stated over the *nullable* cursor, and a C# body has to read
a field through the very same pointer:

```fstar
unfold
let opened (from: class_DNode__opt)
           (prev to_ last: class_DNode__opt) (l: list int) : slprop
  = exists* (r: class_DNode__raw) (tl: list int).
      B.pts_to from r **
      dll_seg 1.0R r.fld_next from to_ last tl **
      pure (l == I32.v r.fld_value :: tl /\ r.fld_prev == prev)
```

Under R10.2 this is straightforward: `DNode` and `DNode?` are one Pulse type, so the cursor
the contract talks about *is* the reference the field access reads through. The C# call is
`Open(from, …)` and the resulting `B.pts_to` is syntactically at `var_from`, which is what
the emitter's field reads (R10.4) ask for. Note that the tail segment's `prev` is `from`,
which is what lets the recursive call `Length(from.next, from, last)` match with no
`rewrite` at the call site.

> *A cursor is named **once**, which is worth saying because it was not always possible.
> While `C?` was `option class_C`, a non-null cursor needed a binder
> `(from: class_DNode__opt { Some? from })` — a refinement C# cannot declare — so predicates
> named the head twice and every call site read `Open(from, from!, …)`. R10.2 removed the
> two types and with them the two names. The doubling that remains is a different thing and
> is not removable: a value the body learns by **reading the heap** — a `next` field, a
> payload — must be named explicitly if a later step is to take it back as an ordinary
> argument (F73).*

One convention has to be observed on the F* side. R4.13 sends a C# `int` into a
specification as its mathematical value, so a predicate parameter a C# `[SpecOp]` passes an
`int` to must be declared `int`, not `I32.t`, with the machine value existentially bound:

```fstar
unfold
let cell (v: class_DNode) (value: int) (prev next: class_DNode__opt) : slprop
  = exists* (x: I32.t).
      B.pts_to v ({ fld_value = x; fld_prev = prev; fld_next = next }) **
      pure (I32.v x == value)
```

Declaring the C# parameter `SpecInt` rather than `int` says the same thing on the C# side and
is the clearer of the two.

### 12.6 Status

Pinned first, and independently of the compiler, by `test/pulse_facts/SegmentFacts.fst`:
§§1–5 give the representation exactly as the emitter produces it, `dll_seg`, the whole-list
wrapper, all eight lemmas, a forward traversal and a `push_front` that writes the old head's
back pointer; §6 pins R12.7's C# face — `opened`, `cell`, `seg_open`, `seg_close`, `seg_cons`
— and redoes both worked programs with **no `with` and no `rewrite` in the caller**. That
§6 verified on the first attempt is the fact the whole of M10 rests on: Pulse's matcher does
cope with the read-then-recurse pattern, so the only thing the lemmas must absorb is the
nullable-cursor-to-boxed-node conversion.

Delivered end to end from C#: `test/dll_segment`. `DllSeg.fst` is the predicate and its
lemmas as a real F* file, pulled in by `[assembly: IncludePulseFile("DllSeg.fst")]`. `Dll.cs`
declares `[Plain] DNode`, gives the predicate a C# face as four `SlProp`-valued `[SpecOp]`s,
and publishes four `[Lemma]`s — `Cases`, `Open`, `Close`, `Cons` — one per step a body takes.
`DllOps.cs` has a recursive `Length` over a segment and a `PushFront` that allocates a node
and **writes the old head's back pointer** — the operation a doubly linked list exists for,
and the one §10 could not reach at all. Between them the two bodies contain exactly one raw
`Pal.GhostStmt`, `unreachable ()`, in a branch the user's own `Cases` lemma has just shown to
be dead.

The §7.2 detector applies: `DllOpsVariant.cs` is the same two operations written with the
null tests inverted and their branches swapped, the cursor read into a local before the
recursive call, the allocation moved past the case split, the locals renamed and the addition
written the other way round — and with the null test spelled the other way about, which
R10.2c makes the same translation. It verifies with no emitter change. Two
diagnostics cases cover PALCS0574 and PALCS0575.

What §12 does *not* do is make the proofs disappear. A segment operation still costs the user
four or five explicit proof steps. What R12.7 changes is *where they live and what they look
like*: they are now typed C# calls to lemmas the predicate's author published once, rather
than `rewrite`s the caller has to rediscover. That is §0 rule 3 working as intended — the
difficulty is in the user's annotations and in a reusable library, visible and editable,
rather than in a special case in the emitter. The cheap path remains §10, and §11 widens what
§10 can be cheap about; §12 is what you reach for when neither will do.

---

## 13. Conversions, side effects, and a production case study

§§1–12 were exercised on programs written to be verified. §13 is the first section driven
by code that was not: SharpZipLib's `Adler32` (MIT), verified in `examples/adler32`.

That directory is the reason `examples/` exists. An example and a test run through the
same harness (`test/verify.mk`), carry the same two obligations, and are gated by the same
`make test`; what separates them is provenance. A test is written to exercise a numbered
rule and may be shaped to do so. An example is code that was written for some other
purpose, ported with its adaptations documented and its upstream licence carried alongside
it (`examples/adler32/LICENSE`), and it may not be reshaped to suit the tool. Gating them
identically is the point: an example that is allowed to rot is a claim about pal-csharp
that stopped being true without anyone noticing.

The target was chosen for one reason. Most C# checksums — MurmurHash3, the two common
CRC32s, FNV-1a — rely on **intentional wrapping**, so the obligation pal-csharp discharges
(absence of overflow) is the wrong one for them, and their specification ("it matches the
reference definition") is close to circular. Adler-32 is designed to *avoid* overflow, and
the production source carries a hand-written safety argument in a comment. There is
therefore something specific to check rather than merely a definition to restate.

### 13.1 What the case study found

The comment reads:

```
// We can defer the modulo operation:
// s1 maximally grows from 65521 to 65521 + 255 * 3800
// s2 maximally grows by 3800 * median(s1) = 2090079800 < 2^31
```

Its conclusion is right and its figure is wrong (F54). The true supremum of `s2` is
**2 090 626 020**, larger than the stated 2 090 079 800 by **546 220**, because
"median(s1)" approximates a triangular sum. The comment *understates* the maximum — the
direction that would have mattered had the margin been thinner. The real headroom against
2^31 is 2.65%, not 2.68%. The `s1` claim (max 1 034 520) is correct.

The arithmetic was pinned in `test/pulse_facts/ConversionFacts.fst` **before** any emitter
code was written, per §0. That is the order the discipline requires and it paid: the
case study's headline finding is machine-checked and independent of everything below it.

### 13.2 Rules

| Rule | Construct | Translation |
|---|---|---|
| **R13.1** | explicit numeric cast `(T)e` | `Cast.<src>_to_<tgt> ⟦e⟧`, from `FStar.Int.Cast`. **Modular, with no precondition** (F46). An explicit cast is the programmer *asking* for truncation, and C#'s default `unchecked` context defines it to truncate; demanding `0 <= v < 256` at a `(byte)` cast would be the emitter inventing a refusal for an operation the source language defines (§0 rule 3). A user who wants exactness proves the range and F49 hands it back. |
| **R13.2** | a conversion in *specification* position | the identity on the mathematical value iff every value of the source type is a value of the target (F47) — **not** merely "the target is wider". Otherwise `% pow2 n` (unsigned target) or `FStar.Int.op_At_Percent` (signed) (F48). `Types.RangeFits` decides. |
| **R13.3** | `x++`, `++x`, `x--`, `--x` in expression position | an `IrStmtExpr(prelude, value)`: the write is emitted **at the operator's own position in the tree**, not hoisted to a statement before the enclosing one. The node therefore inherits the emitter's left-to-right operand order and R6.3's short-circuit capture for free, and is faithful by construction with no side condition. Hoisting would have been wrong for `p && a[i++] > 0`. In specification position the construct is refused (PALCS0576): a specification denotes a state and never changes one. |
| **R13.4** | implicit numeric promotion | recorded as an `IrConvert` at the same place reference conversions are. C# evaluates `byte & int` at `int` width — both operands promoted, `int`'s operator applied — and the promotion must be translated or the emitted term is ill-typed. **Literals are re-typed, not converted**: `byte b = 5;` converts at compile time, and emitting a cast would name a runtime operation the program does not perform. |
| **R13.5** | shift | `FStar.UIntN.shift_left` takes a `UInt32.t` amount whatever the operand's width (F51), so the *amount* — and only the amount — carries a conversion. |
| **R13.6** | argument to a `[Spec]` function or `[Lemma]` | a machine argument crosses into the mathematical world exactly when the binder it is passed to lives there. R4.6 makes every `[Spec]` parameter mathematical whatever its C# type; R4.7 leaves a `[Lemma]`'s binders as declared (F55). `IrCall.ParamTypes` carries the declared types so the decision is made per parameter, in one place, for calls from specifications and from code alike. |

R13.6 replaced a blanket rule that coerced every machine argument. That was sound for
`[Spec]` calls, which are the only kind a specification could make before M7, and silently
wrong for a `[Lemma]` with a machine parameter — a combination `examples/adler32` is the first
program to write.

### 13.3 What Adler-32 needed, and where each piece landed

Every gap was closed at the layer §0 rule 3 names, and none in the emitter:

| Gap | Fixed in |
|---|---|
| `Seq.length` unbounded, so `offset + 1` might overflow | `Pulse.Lib.CSharp.Array.arr_length_bound` — **library** |
| nothing tied `A.length buf` to `Seq.length` | `Pal.GhostStmt("Pulse.Lib.Array.pts_to_len $&(buf)")` — **user annotation** (and it forced `$&(…)`, documented in `doc/surface_syntax.md` since M1, to actually be implemented) |
| `(uint)(b & 0xff) <= 255` | `Pulse.Lib.CSharp.Casts.byte_mask_ff_bound`, with an SMTPat **on the idiom** (F53) — **library**, and so free of annotation |
| `(s2 << 16) | s1` denotes `s2 * 65536 + s1` | `Pulse.Lib.CSharp.Casts.logor_shift_disjoint`, likewise patterned on the idiom — **library** |
| the loop maintains congruence, not equality | `ModAdd`/`ModIdem`/`Step` as `[Lemma]`s in the user's own file — **user annotation** |

The last row is the substance of the proof, and it is worth stating plainly, because it is
what makes a deferred-modulo checksum verifiable at all:

> The loop reduces `s1` and `s2` at every chunk boundary; the specification reduces only
> at the end. So what the loop maintains is not equality with the specification but
> **congruence mod BASE** — and congruence is exactly the relation that survives both
> operations the loop performs, adding a byte and reducing.

A corollary caught a real error in a first attempt. `s2 += s1` adds a value that is only
*congruent* to the specification's accumulator, never equal to it, so the step needs
congruence on **both** summands:

```csharp
[Requires("a % BASE == b % BASE")]
[Requires("c % BASE == d % BASE")]
[Ensures("(a + c) % BASE == (b + d) % BASE")]
```

The four-argument form is the honest one; the three-argument form (`c` added to both
sides) is only enough for `s1`.

### 13.4 What was proved

`Func_Adler32_Update` verifies, in two tiers:

* **Tier A — safety.** No array access out of bounds, no arithmetic overflow anywhere,
  including across the deferred modulo. The invariants that carry it are linear in the
  work remaining, which is what lets each survive a single iteration:

  ```csharp
  Pal.Invariant(s1 <= BASE - 1 + 255 * (NMAX - n));
  Pal.Invariant(s2 <= BASE - 1 + (NMAX - n) * S1MAX);
  ```

  The coarse `s2` bound is 3 931 241 520 < 2^32, which is what the `uint` the code
  actually uses requires. The *tight* 2^31 analysis the comment attempts lives in the
  probe, where F54 records that the comment gets it wrong.

* **Tier B — functional correctness.**
  `Result == Adler(Old(Contents(buf)), Old(offset), Old(count))`, where `Adler` is RFC 1950
  §8.2 stated inductively in C# as two `[Spec]` functions. This is the postcondition
  §specreview asks for: it relates the output to the *input*, not merely to a type.

### 13.5 The §7.2 detector

`examples/adler32/Adler32Variant.cs` is the same checksum with the inner loop written as a
`for`, the chunk size chosen by a conditional expression rather than an `if` statement, the
accumulators updated by compound assignment, the outer guard written `!= 0`, and every
local renamed. **It translated with no emitter change** — which is the claim §7.2 exists to
test. It needed five `Pal.Assert`s the original does not, splitting the invariant's
re-establishment into its conjuncts, because the conditional chunk size reaches the solver
as a `match` term it must case-split. That cost is charged in the annotations, where §0
rule 3 says it belongs.

### 13.6 One place fidelity was traded, and why

SharpZipLib writes the inner loop as `while (--n >= 0)`. pal-csharp **translates** that
faithfully after R13.3, but the result is hard to *specify*: Pulse requires the stateful
guard to preserve the invariant, and the natural progress invariant is not stable under the
guard's own decrement. Only inequalities in the weakening direction survive it, and the
body cannot re-establish a tight bound because `n` is stale by one inside the body — the
decrement happened in the guard, not the body. The textbook resolution is to move the
decrement out of the guard, and that is what `examples/adler32/Adler32.cs` does:
`while (n > 0) { …; n--; }`.

This is the one adaptation to the loop, and it is a genuine, reportable limitation rather
than a translation gap. `offset++` inside the array subscript **is** retained, so R13.3 is
still exercised by the real idiom. Two further adaptations are mechanical and touch only
the signature: `ArraySegment<byte>` is spelled out as `(buf, offset, count)`, and the
instance field is passed and returned rather than mutated.

---

## 14. Unconstrained generics

F62–F64 measured the cost of a C# type parameter before this section was written, and the
measurement is what fixes its shape: `Pulse.Lib.CSharp.Array` is already `(#t: Type0)`, a
generic struct is an ordinary parameterised record, and instantiation composes. So generics
add binders and applications to the existing scheme and change no rule that is already here.

### 14.1 What is in scope

**R14.1 — A type parameter is translated exactly when it is unconstrained.** A `where`
clause is a typeclass obligation: `where T : IComparable<T>` says a call to `CompareTo`
must resolve through a dictionary that the caller supplies, and neither the dictionary nor
its coherence has been probed. A constrained type parameter is refused (PALCS0580) rather
than translated with the constraint dropped, because dropping it would silently admit a
program whose body cannot be written.

This is a smaller subset than it sounds, and a well-defined one. C# permits almost nothing
on an unconstrained `T` — no comparison, no arithmetic, no member access, not even `==`.
What is left is the *element-agnostic* part of the language: moving values into and out of
arrays, holding them in a container, counting them, copying them. That is precisely the
part `Span<T>`, `ReadOnlySpan<T>` and `ArraySegment<T>` inhabit, and `examples/adler32`
had to spell its segment out by hand for want of it.

**R14.1b — `Ghost<T>.Value` is transparent.** `Ghost<T>` erases to `T` in a type (R14.1) and
a spec string is bound against parameters that are *already* unwrapped, so a spec string
never writes `.Value` at all. But a specification written in **statement position** —
`Pal.Invariant(…)`, `Pal.Decreases(…)`, a `[Lemma]` argument — is an ordinary C# expression,
where `Ghost<T>` is a real type and C# demands the projection. Nothing about the *meaning*
changes when it is written, so nothing in the translation does either: `g.Value` lowers to
whatever `g` lowers to.

### 14.2 Type parameters are binders

**R14.2 — A method's type parameters become explicit `Type0` binders, ahead of every value
parameter, in declaration order.** `static void Swap<T>(T[] a, int i, int j)` emits

```
fn func_Swap (ty_T: Type0) (var_a: array ty_T) (var_i: I32.t) (var_j: I32.t)
```

A type binder is also bound **in the specification scope**, so R4.9's `$(T)` resolves to
`ty_T` exactly as `$(x)` resolves a value parameter. Without it a generic `[Lemma]` whose
value arguments do not mention `T` — an introduction rule for the empty case of a predicate,
say — has no way to say which type it is about, and the implicit is left as an unresolved
uvar (*"Unexpected unresolved uvars"*). A type parameter is a C# name in scope; `$(…)`
resolves C# names in scope; the rule is the absence of an exception.

They are *explicit*, not implicit `#`-binders, and that is a deliberate choice against the
F* idiom. Roslyn has already resolved the type argument at every call site — for an
inferred call as much as for `Swap<int>(…)`, since C# type inference runs at compile time —
so the translation has the answer in hand and emitting it is structure-preserving. Relying
on F*'s inference instead would make the emitted program's well-typedness depend on a
second inference algorithm agreeing with C#'s, which is a thing to be avoided rather than a
thing to be hoped for. It also keeps a type parameter that appears in no parameter type
translatable rather than being a special case.

Both forms were probed (`test/pulse_facts/GenericFacts.fst` uses implicit binders;
`BinderProbe` confirmed the explicit form, its application at a concrete type, and a generic
caller passing its own type variable along).

**R14.2a — `default(T)` at a type parameter is the caller's to supply.** Its value
depends on what `T` is (`null`, `0`, `None`, …), so a method that takes `default` at a
method type parameter `T` gets a typeclass binder `{| _: Inhabited.has_default ty_T |}`
after the type binders, and `default(T)` is `Inhabited.default_of ty_T`. A caller at a
concrete type has the instance resolved by F\*, from `Pulse.Lib.CSharp.Inhabited`'s
instances (`option`, the machine integers, `bool`, …); a generic caller passes its own.
The binder is added only where the body (or an expression body) takes a `default`, so
generic code that never does is unaffected.

**R14.2b — A specification's shim is generic in the same parameters.** R4.x binds an
attribute's spec string by generating a shim method whose parameters are the annotated
method's, and compiling it. A spec on a generic method mentions its type parameters —
`[Ensures("Contents(a) == …")]` on `T[] a` cannot be *typed* without `T` — so the shim
carries the same type parameters, by name. It carries no constraints, and needs none:
R14.1 admits only unconstrained parameters, so a spec that would require one is already
refused at the declaration. This is the only place in the pipeline where generics are not
simply "a type like any other", and it is a consequence of specs being bound as real C#
rather than parsed.

**R14.3 — A type parameter `T` is named `ty_T` in Pulse.** F* reserves an initial capital
for constructors and modules, so `T` cannot be a binder name. The prefix follows the
existing conventions (`var_`, `spec_`, `class_`, `struct_`), and the C# name is preserved
after it so that a message about `ty_T` is legible to someone reading `T`.

**R14.4 — A type parameter in type position renders as its binder name.** `T` is `ty_T`,
`T[]` is `array ty_T`, `Seq<T>` is `Seq.seq ty_T`. Nothing else in §3 changes: the type
parameter is a type like any other, and every rule that maps over a type maps over it.

### 14.3 Call sites

**R14.5 — A call to a generic method applies its type arguments first, positionally, in
declaration order.** `Swap(a, i, j)` inside a method with its own `T` emits
`func_Swap ty_T var_a var_i var_j`; `Swap<int>(b, 0, 1)` emits `func_Swap I32.t var_b 0l 1l`.
The arguments come from Roslyn's resolved symbol, so an inferred call and an explicit one
are translated identically — as they should be, being the same call.

This is the rule that keeps R2.x's module-per-method structure intact. F64 pins that
instantiation composes, so nothing needs specialising: one `Func_` module per generic
method, called at every instantiation, exactly as a non-generic method is.

It applies to all three kinds of callee, because all three are the same IR node: a method
(`func_`), a `[Spec]` function (`spec_`) and a `[Lemma]` (`lemma_`). Each therefore takes
its type binders ahead of its value binders by R14.2, and each is applied to its type
arguments here. A generic `[Spec]` function is worth calling out: it is what lets the
*specification* of a generic method be written once — `Interchanged<T>(s, i, j)` is a
sequence-valued function of `T`, and without R14.2 on spec functions every postcondition
would have to be inlined at each use.

### 14.4 What is refused

Each of these is a refusal to *translate* — a construct with no image under the rules above
— and not a prediction that a proof will fail (§0 rule 3):

* **A constraint (PALCS0580).** R14.1. Includes `where T : class`, `struct`, `new()`, a base
  type and an interface: each says something about `T` that the translation would have to
  carry, and none has been probed.
* **A generic type declaration (PALCS0581).** A generic `class` or `struct` needs a
  parameterised record *and* a parameterised invariant, and §3.4's class encoding fixes the
  representation type at the reference type. F63 shows the record is available; the
  invariant is not yet designed, so the declaration is refused rather than half-translated.
  A generic *method* on a non-generic type is unaffected, which is where the value is.
* **A generic local function or lambda.** Neither exists in the supported subset already.

A type parameter used as the receiver of anything, or compared with `==`, needs no rule
here: C# itself rejects it, so it cannot reach the translation.

---

## 15. Generic types

M8 refused a generic class or struct declaration (PALCS0581) on a stated ground: the record
is representable (F63), but "the invariant and the ownership predicate of a type
parameterised by a type have not been designed". F66–F70 design them. The refusal was
honest and is now discharged, which is the only way a refusal in this document is ever
meant to be removed.

The whole of §15 is one observation. A class's F\* image is a *family* of definitions — a
record, two abbreviations, a model type, an invariant, six case lemmas, two permission
lemmas — and every one of them either mentions the class's representation type or is a
predicate over it. So parameterising the class parameterises all of them uniformly, and the
question is only where the argument has to be written down.

### 15.1 Where the parameter is written

**R15.1 — A class's or struct's type parameters become binders on every definition its
module emits, in declaration order.** The record, the `box` abbreviation, the `option`
abbreviation, the model type, the invariant, the case lemmas and the share/gather lemmas
all take them. R14.1 applies unchanged: a constrained parameter is refused (PALCS0580).

**R15.2 — On a *type* definition the binders are explicit; on everything else they are
implicit.** This is the one rule of §15 with a choice in it, and F68 is why it goes this
way.

A type has no value argument to infer from, so `class_Node__opt` must be applied: a method
binder reads `(var_n: class_Node__opt ty_T)`. Everything else — the invariant, and all
eight lemmas — has a value argument whose type already mentions the parameter, so the
argument is determined by unification with something the emitter is writing down anyway.
Making it explicit would be writing the same information twice.

That is not a stylistic preference. §10's client rules emit lemma calls by the hundred
(`class_Node__cases var_n;`, `class_Node__elim_cons var_n;`, `class_Node__intro_cons
var_n;`), each in a context where the emitter has a *C#* type in hand and would have to
render its F\* image to supply an argument. Under R15.2 not one of those call sites
changes. The client half of §15 is therefore almost empty, and that is the rule's whole
justification.

Contrast R14.2, which made a *method*'s type parameter explicit. The two rules disagree
because the two situations do: Roslyn resolved a method's type argument and the emitter has
it, whereas a generated lemma's type argument is a function of an argument already present.
Neither rule is asking F\* to guess.

**R15.3 — A class type is named with its type arguments applied.** `Node<T>` inside a
generic method is `class_Node__opt ty_T`; `Node<int>` in a non-generic one is
`class_Node__opt I32.t`. The arguments come from Roslyn's constructed type symbol, so — as
in R14.5 — an inferred instantiation and a written one are indistinguishable by the time
the translator sees them.

**R15.4 — The recursion is at the same type argument.** A recursive field of `Node<T>` has
type `Node<T>?`, never `Node<U>?`, because that is what C# writes: a field's type is a type
in the class's own scope. So the mutually recursive group is parameterised uniformly and
F66's well-foundedness argument is the monomorphic one.

This is worth stating because the alternative — *non-uniform* (polymorphic) recursion, as
in `Nest<T> { Nest<(T,T)>? next; }` — is expressible in C# and has no `type … and …` image
at all. It is refused (PALCS0582): a field whose type instantiates the enclosing class at
anything but its own parameters.

### 15.2 What the model is

**R15.5 — A generic class's model type is parameterised by the same parameters.** R10.5
reads the `[Model]` member backwards to obtain the induction, and the constructor
application it reads is now at the element type: `SpecList.Cons(value, next!.Items)` where
`value` is a `T` gives `list ty_T`, and the pure conjunct relating the head to the field is
`m0 == r.fld_value` rather than R6's `I32.v r.fld_value`, because there is no conversion to
apply at an abstract type.

That last clause is not a special case. §6 puts `I32.v` on an integer field because a C#
`int` field and its `SpecInt` model are different types; a `T` field and its `T` model are
the *same* type, so the identity is what §6 already prescribes.

### 15.3 Saying things about an abstract value

**R15.6 — Equality on a type parameter is `Pal.Same(a, b)`.** C# refuses `a == b` on an
unconstrained `T`, so a specification that needs it has nothing to write; `Pal.Same` is a
`[Spec]`-level intrinsic that lowers to `BinOp.Eq` and is otherwise a `==`. It exists for
exactly the reason the rest of §15 does: the C# surface is missing an operator that the F\*
image has, and the annotation layer is where that gap is filled.

`test/generic_tree`'s `GetOr` is the case: it returns a `T`, and
`Pal.Same(Result, SpecTree.Get(t.Elements, k, fallback))` is its whole postcondition.

**R15.7 — The list vocabulary lives in `Pulse.Lib.CSharp.List`.** `SpecList.Take`, `Drop`,
`InsertAt`, `RemoveAt` and `Reverse` denote `CL.take`, `CL.drop`, `CL.insert_at`,
`CL.remove_at` and `CL.rev`. Every one is **total and takes an `int`, never a refined
`nat`**, and that is a rule rather than an omission: R3.9b puts a method's precondition in a
*later* conjunct than the postcondition that mentions these terms, so `CL.take m (I32.v
var_i)` has to be well typed where a bound on `var_i` is not yet available. Clamping a
negative or oversized index is therefore part of the specification, and the library says
what the clamp does.

**R15.8 — `null` at a generic class is named before it is introduced.** `None` says nothing
about what it is empty *of*, so R15.2's implicit type argument to `class_C__intro_nil` has
nothing to resolve against. The emitter binds it first, at its type
(`let t : class_C__opt ty_T = None;`), and introduces the invariant at the binder. A
monomorphic class has no ambiguity and keeps the shorter form, so every pre-M9 emission is
byte-identical.

**R15.9 — A type in argument position is bracketed.** `tree (kv ty_T)`, not `tree kv ty_T`.
This is R15.3 applied one level down, and it is what makes a *nested* generic specification
type — a map is `SpecTree<SpecKv<T>>` — render correctly.

### 15.4 What stays refused

* **A constrained type parameter (PALCS0580).** R14.1, unchanged. This is what keeps an
  ordered container generic in its *value* and concrete in its *key*: a `TreeNode<T>` with
  an `int key` and a `T value` is a map, is fully general in what it stores, and needs no
  comparison on `T` at all. A `TreeNode<T>` ordered *by* `T` needs `IComparable<T>` and is
  refused.
* **Non-uniform recursion (PALCS0582).** R15.4.
* **A generic `struct` (PALCS0581).** A struct is a *value* here: copied at every
  assignment, stored inline in whatever holds it, and represented by R3.4's record rather
  than by a reference with an invariant. Parameterising a record is a different problem
  from parameterising a class and has not been designed.
* **A generic class in a hierarchy (PALCS0581).** §9's vtable is a record whose field types
  mention the class, so parameterising the class parameterises the vtable, and the cast
  lemmas relating a derived record to its base have to be parameterised alongside it.
  Neither is designed. The refusal fires at the derived class too, so that no hierarchy
  anywhere contains a parameterised class.

§11's user-defined specification types are *not* on this list: `[SpecType]` has always been
generic where the F\* type behind it is, and R15.9 is what makes the nested case
(`SpecTree<SpecKv<T>>`) come out right.

### 15.5 What §15 does not reach

Three shapes are expressible in C#, are not about generics at all, and are refused or fail
for reasons §10 and §4 own. They are recorded here because they are what a "complete"
container library runs into, and because the honest response to each is a rule, not an
emitter patch.

* **A field read through a non-null recursive reference.** R10.7 opens a window at a *null
  test*, so a receiver of type `Cell<T>` (not `Cell<T>?`) has no window to be read in.
  This is why `test/generic_list` has no `First`. The rule that would fix it — open a
  non-null receiver directly with `as_opt`, `cases` and `elim_cons` — is designable and is
  not designed.
* **A windowed reference passed as an argument.** R10.7 closes the window at the end of the
  branch, so a reference handed to a call *while open* is handed over open. This is what
  makes an in-place `Reverse` (which passes `x` to its own recursive call after rewriting
  `x.next`) fail, and why `test/generic_list`'s `Reverse` is the persistent one.
* **A `[Consumes]` parameter given away on two different paths.** R4.9c is a statement about
  the *method*: the first consuming use moves the argument, and a second use is PALCS0550
  even when the two are in disjoint branches. Splitting the branches into two methods says
  one thing each, and is what `test/generic_list` does.

The persistent style these push a library towards is not a consolation prize. An operation
that allocates what it returns leaves its argument `[Frac]`-observed, so the caller keeps
the list it passed in — which is the ordinary contract of a container operation in a garbage
collected language, and the one C# programmers expect.

---

## 16. Cursors: iterative traversal

§10.7 refused iterative traversal and gave a reason — *"needs a magic wand to give the tail
back, and has not been probed"*. §12 then answered the first half without noticing: a
**segment** predicate is what a magic wand was wanted for, and `test/dll_segment` already
had one. §16 probes the rest. The refusal is discharged, and it is discharged the way §0
asks — a probe first, then rules, then two acceptance directories and their variants.

The section's one observation is this:

> **The part of a structure a loop has walked is a function of the loop counter, not a
> history.** So it can be *named* in the invariant by a total function of the counter, and
> the loop needs no ghost accumulator, no wand, and no rule beyond R5.8c.

### 16.1 The linear case

`test/list_cursor` walks a singly linked list. The user's Pulse file `CellSeg.fst` declares
one predicate, `seg p from to_ l` — the cells from `from` up to (not including) `to_`, and
the values in them — plus `whole = seg from None`. The loop invariant then owns two halves:

```csharp
Pal.Invariant(Cells.Seg(head, at, SpecList.Take(xs.Value, i)));   // walked
Pal.Invariant(Cells.Held(at, SpecList.Drop(xs.Value, i)));        // remaining
```

`Take` and `Drop` are the two total functions of the counter. Advancing is `seg_snoc` —
moving one cell from the right half to the left — and finishing is `seg_close`, which is the
"magic wand" §10.7 wanted, except that it is an ordinary lemma about an ordinary predicate
and needed no wand at all.

### 16.2 The branching case

`test/tree_cursor` walks a binary search tree. Nothing about the shape of §16.1 changes; the
walked part is just a **one-hole context** rather than a prefix. `KnotPath.fst` declares

| linear | branching |
|---|---|
| `SpecList.Take(xs, i)` | `Descent.Ctx(t, key, n)` — the spine, outermost-first |
| `SpecList.Drop(xs, i)` | `Descent.Sub(t, key, n)` — the subtree still to search |
| `Append` | `plug c sub` |
| `seg_snoc` | `path_append` — one frame appended to the spine |
| `seg_close` | `path_close` |

The frame carries the node's key, its value, and **the off-path child**, so a step down owns
the sibling subtree it did not take. A descent's path is in general path-dependent, but a
*search* path is determined by the tree and the key, both of which are fixed for the loop —
so `Ctx` and `Sub` really are functions of `n`, and a branching cursor needs no more loop
machinery than a linear one.

Two details are worth pinning because they were not obvious:

* **`Sub` and `Ctx` recurse on the tree, not the counter** (`decreases t`), so `n` stays an
  unrefined `int` and no `n <= depth` refinement has to be threaded. They stop early at a
  hit, which is what makes `Sub`'s relationship to `kfind` hold unconditionally.
* **No ordering hypothesis is needed.** `kfind` on a `Branch` is *defined* by comparing the
  key with the entry, so following the comparison is following the definition. An
  out-of-order tree makes lookup useless, not unsound — and a precondition demanding
  sortedness would have been a proof obligation invented for the emitter's convenience.

### 16.3 Rules the cursor needs

**R16.1 — Two exits, no `break`.** `break` is R5.10, which allocates a flag; a loop with a
data-structure invariant does not need it. The device the probe pinned instead: an `int`
local `live` is the loop condition, and the measure is `size(Sub(t, key, n)) + live`. A
descent shrinks the subtree; a stop clears the flag; either strictly decreases the sum. This
is general to any pal-csharp loop with an early exit, and it is written by the user, not by
the emitter.

The measure **must** use the walked structure's size, not the counter: R5.9's case-2
measure bounds a counter by its own type, and a tree has no length by which to bound `n`.
`Pal.Decreases` (R5.9 case 1) is how a user says so.

**R16.2 — Every conjunct of an invariant must be distinguishable by its resource.** Pulse
matches by resource, so two conjuncts of the *same* predicate whose only difference is an
argument the body just read from the heap cannot be told apart. The fix is not a lemma but a
definition: make each conjunct's model half a **total projection** of a model the invariant
already names — `subl t` and `subr t` rather than two existentials. Then the two conjuncts
differ syntactically and the matcher never has to guess.

**R16.3 — An existential reachable only through `pure` can never be solved.** Pulse's
matcher recovers an `exists*` binder from the `pts_to`s it unifies. A binder that appears
*only* inside a `pure (…)` has nothing to be recovered from, and folding such a predicate
fails with *"Cannot check relation with uvars"*. This decides where a machine value may be
hidden:

* a predicate that is **folded** by a body — one that describes an open node — keeps its
  machine field explicit, because the record literal determines it; a wrapper with
  `exists* (k: I32.t)` then hides it for the invariant's benefit, and the matcher recovers
  `k` from the `pts_to`;
* a predicate only ever **matched as a precondition** may take a mathematical `int` with the
  machine value existentially bound, because the caller's context supplies it. `DllSeg.cell`
  is this shape.

R10.2 removed the commonest instance of this rule. Under the option encoding *every*
recursive invariant's cons case bound a node existential reachable only through
`pure (x == Some v)`, so every user predicate imitating one inherited the problem and every
lemma over it needed the cursor twice. The box encoding puts the `pts_to` at the cursor
itself, so nothing has to be recovered. What survives is the case the rule was really about:
a value the body learns by *reading the heap* and a later step takes back as an argument.

**R16.4 — A model-level guard is stated over the model.** R4.13 sends a C# `int` in
specification position into F\* as its `.v`, by *position* and not by declared type, so a
predicate parameter of type `I32.t` is unwritable from a C# contract. The consequence is a
style rule, not a limitation: publish a total projection of the model (`Descent.NodeKey`)
and let the contract compare against **that**. The body's own `key < nk` on machine ints
implies it, because the open-node predicate ties the field to the model. The signatures get
shorter, and the contract stops mentioning machine words.

**R16.5 — A pure lemma call goes first.** A pure `Lemma` placed *last* in a `ghost fn` body
has its postcondition dropped. Call it before the step it justifies.

### 16.4 What is delivered

`test/list_cursor` — `CellSeg.fst`, `Cell.cs` (the `[Plain] Cell<T>`, five `[SpecOp]`s and
six `[Lemma]` steps), `Walks.cs` with an iterative `Count`, and §7.2's `WalksVariant`.

`test/tree_cursor` — `KnotPath.fst`, `Knot.cs` (the `[Plain] Knot<T>`, the `SpecFrame<T>`
spec type with its two `[SpecCtor]`s, and ten `[Lemma]` steps), `Search.cs` with an
iterative BST `Find` proved to return `SpecTree.Get(t, key, fallback)`, and §7.2's
`SearchVariant` — which builds its tree by nesting constructor calls, tests membership
rather than lookup, spells the comparison the other way round, checks equality last, and
names its flag differently. It verifies with no emitter change.

The emitter changes §16 required are R5.8c, R5.8d, R12.3b, R12.3c and R14.2's scope
extension. Every one of them is a rule about a C# construct — an invariant clause, a tail
position, an assigned local, a null test, a name in scope — and none mentions a cursor.
Everything that *is* about cursors is in the user's Pulse file and the user's annotations,
which is what §0 rule 3 asks for and is the whole claim of §16.

### 16.5 What §16 does not reach

* **A cursor that mutates.** Every step here is `[Frac]`-observing or full-permission
  read-only; an iterative in-place insert would have to re-close the spine around a *changed*
  subtree, which is a different `path_close` and is not probed.
* **A cursor over a structure the compiler derives.** §16 is written entirely against §12's
  user-defined predicates. A `[Recursive]` class's derived invariant still has only R10.7's
  window, so §10.7's refusal stands for *derived* structures — narrowed, not removed.
* **`break`.** R16.1's flag is the idiom; making R5.10's flag interact with an owning
  invariant is untried.

## 17. `Span<T>`: a borrowed window

The facts were probed and pinned first (`test/pulse_facts/SliceFacts.fst`, F78–F83), as §0
requires. This section is the scheme they led to.

A `Span<T>` is a **borrowed window** into memory somebody else owns. That is what the C#
type means and it is what `Pulse.Lib.Slice.slice` is, so the two are put together: §17.2
gives the rules, §17.3 the borrow, §17.4 what is refused.

### 17.1 What the probes settled

**A span is a struct that owns memory, so it cannot be a translated struct (F79).** §3.4
rejects a struct field of reference type as `PALCS0511`, because copying the struct would
duplicate ownership of the same memory — and a `Span<T>` is exactly such a struct. Applying
that rule to spans would be correct and useless. A span must therefore be a **slot kind**,
primitive like `T[]`: no field projections, no struct copying, its own row in R4.9's table.
R17.1 makes it one.

**The library is already the right shape (F78).** A `slice t` has a non-ghost `len`, a
`pts_to` over its contents, `split`/`join`, `subslice` with a `subslice_rest` residue,
`share`/`gather`, and an `is_from_array` provenance token. Taking a window and giving it
back are both *derivable* — `SliceFacts` S2 does it — so nothing had to be asked of the
Pulse library. What was missing was only the C# side.

**And the C# side is smaller than it looks.** The question that made this section hard to
write was: C# marks neither the point where a window borrows nor the point where it
returns, and recovering either from flow analysis is a borrow checker, which R10.2b refuses
on principle. Both halves of that turn out to be wrong.

*Borrowing is marked.* `a.AsSpan(1, 3)` is where the author put it, and Roslyn hands it
over as an ordinary expression. No new syntax is needed to take a window because C# already
has the syntax.

*Returning is unmarked because there is nothing to mark.* Ending a borrow has no runtime
content — it is purely a proof step — and a proof step the author writes is a **ghost
statement**, which §12 has supported since M10. So `Pal.Restore(w)` (R17.6), and the borrow
checker never comes up: to choose which restore to emit the translator reads the
*initializer* of the window's local, which is syntax, and reads nothing else.

> ***An earlier draft of this section took a different route,*** and it is recorded because
> the mistake is instructive. Observing that a span which is only passed and indexed *is*
> the array — same address, same length, same contents, same owner — it identified the two,
> translating `Span<T>` to the array slot and refusing every span that was not a whole
> array. That bought three rules which cost nothing to write, and paid for them by refusing
> the operation `Span<T>` exists for: `numbers.AsSpan(1, 3)`, the first thing anyone writes
> with a span, was outside the subset. No further work *inside* the identification could
> have admitted it, because the identification is precisely the assertion that such a span
> does not exist — a boundary correctly drawn around the wrong region. The refusal was
> honest about being a scheme limit rather than a proof failure, which is what §0 rule 3
> asks; what §0 does not ask is that the limit be in a useful place.

**Two mechanical points that survive unchanged.** `s.Length` is an `int` where `Slice.len`
is an `SZ.t`, which is R3.3's bridge again and genuinely free. And Roslyn models `s[i]` as
a call to a `ref T`-returning `get_Item` rather than as an element access, so *recognising*
an element write is frontend work that arrays did not need.

### 17.2 The rules

**R17.1 — `Span<T>` and `ReadOnlySpan<T>` are length-bounded slices.** `MapType` sends
both, at a mappable element type, to `IrSpanType`, which `Names` renders `Span.span ⟦T⟧`.
This refines `S.slice ⟦T⟧` with `SizeT.v (S.len s) < 2^31`.
`T[]` is unaffected and stays `array ⟦T⟧`. A span is therefore its own slot kind
(`SlotKind.Span`), whose resource is `S.pts_to` rather than `A.pts_to` — which satisfies
F79's requirement that a span be primitive rather than a translated struct by making it
primitive, which is what F79 asked for.

This is what a span *is*: a base, a length and a permission, describing memory somebody
else allocated. A window has a length of its own (R17.3), a base of its own (R17.4) and an
owner who is owed it back (R17.6), and `slice` has all three where `array` has none of
them.

The C#-facing operations live in `Pulse.Lib.CSharp.Span`, with verified implementations
over the Pulse library and no span-length axiom, in the style `Pulse.Lib.CSharp.Array`
established — not a new theory. §3.4's struct rules are never reached, because `MapType`
never produces a struct for a span.

**R17.2 — a `ReadOnlySpan<T>` parameter is fractional.** It takes a permission variable and
its post-state model is its pre-state model, which is R4.9's `[Frac]` row. The permission is
the one `[Frac("p")]` names if the parameter carries the attribute, and a generated one
otherwise. Generating it is not a convenience: `ReadOnlySpan<T>` *means* read-only in C#, so
requiring the author to also write `[Frac]` would be the translator asking to be told
something the program already says (§0 rule 3, in the "never invent a refusal" direction).
A `Span<T>` parameter is the full-permission row, and takes `[Frac]` only if written.

**R17.3 — `s.Length` is the span's own length.** `IrLength` again, but emitted as
`Span.length_i32`, which is `Slice.len` composed with R3.3's `SZ.t` → `I32.t` bridge. Like
an array's header field, `Slice.len` is pure and non-ghost, so the guard of a counted `for`
over a span is a pure expression exactly as it is over an array, and R5.9's measure
inference applies unchanged.

The length is the *window's*, not its parent's, which is the point: `a.AsSpan(from, count)`
has length `count`, and a method written over a span never mentions where the window came
from.

**R17.4 — `s[i]` is the slice subscript.** Roslyn models it as a call to a `ref T`-returning
`get_Item` rather than as an element access over an array, so the frontend has to recognise
it; what it lowers to is `IrElement`, emitted as `Span.read` / `Span.write`, with R6.4's two
obligations (`0 <= i` and `i < s.Length`) generated at it unchanged.

`ReadOnlySpan<T>` needs no rule to forbid the write, because C# forbids it: its indexer
returns `ref readonly T` and the C# compiler rejects the assignment. This is the core
invariant paying for itself — the annotated program is an ordinary C# program, so an
ordinary C# rule is available to enforce a separation-logic one.

**R17.6a — a span parameter reaches the specification shim as an array.** §4's shim (the
generated compilation unit that binds spec strings, `SpecBinder`) declares a span parameter
as `T[]` rather than as the span type the method wrote. This is the one place the abandoned
identification survives, and it is forced rather than chosen. `Span<T>` is a
`ref struct`, and C# refuses a `ref struct` inside a lambda — *"cannot use parameter that
has ref-like type inside an anonymous method, lambda expression, query expression, or local
function"*, CS9108 — so a shim that kept the span type would reject every quantified
contract, `Forall((int k) => … Contents(a)[k] …)` being the shape almost every array
contract in `test/` has. With the array type the restriction never arises, and no spec term
changes meaning, because `Pal.Contents` has the same `Seq<T>` for both — the shim binds
names and types for a spec string, and never sees a resource at all, so nothing about
ownership rides on the choice.

The restriction does bite in **statement** position, where there is no shim: a
`Pal.Invariant(Pal.Forall(…))` that mentions a span is a real lambda over a real
`ref struct` and C# rejects it. The idiom is to name the predicate — a `[Spec]` method over
`Seq<T>`, which moves `Pal.Contents(a)` out of the lambda and into an ordinary argument
position — and `test/array_view` uses it for exactly this reason. This is a genuine narrowing of
the surface for spans relative to arrays; it is C#'s and not the scheme's, and §17.5 records
it rather than hiding it.

### 17.3 Creation is a borrow

**R17.5 — every span comes from somewhere, and taking it consumes the source.** There is no
way to make a span out of nothing (R17.7 refuses the one C# offers), so every span
expression in the subset names a source that already owns memory, and taking the window
takes that ownership. Five C# forms, three library operations, one receipt each:

| C# | operation | receipt left in context |
|---|---|---|
| `Span<T> s = a;` and `a.AsSpan()` | `Span.of_array a` | `S.is_from_array a s` |
| `a.AsSpan(i)`, `a.AsSpan(i, n)` | `Span.of_array_range a i n` | `Span.is_range_of a w p i j v` |
| `s.Slice(i)`, `s.Slice(i, n)`, `s[i..j]` | `Span.sub s i n` | `Span.is_sub_of s w p i j v` |

The one-argument forms synthesise the missing length as `source.Length - start`, so
`s.Slice(i)` and `s.Slice(i, s.Length - i)` translate to the same term — two spellings of
one operation, which is what §0's structure-preservation rule requires of them.

The borrow is emitted **at the local's own binder**, not at a fresh temporary the local is
then bound to. This is R12.4's reason verbatim: Pulse matches resources by name (F77), so a
copy would leave the context holding `S.pts_to t0 _` while every later mention of the
window asked for `S.pts_to var_w _`.

Consuming the source is what makes the accounting work, and it is visible in the C# type
system rather than enforced by the translator: while the window is out, the source has no
`pts_to`, so an index of it does not verify. The author gets it back with R17.6.

**R17.6 — `Pal.Restore(w)` ends a borrow.** It is a `[Conditional("PAL")]` ghost statement
(§12), so it is erased by the C# compiler and costs nothing at runtime, and it takes **one**
argument: the window. Which of the three operations R17.5 lists is emitted comes from the
`SpanOrigin` recorded on the local's slot **when the local was declared** — a syntactic
property of its initializer, read once, never a flow analysis. After the restore the slot
leaves scope, so a later use of `w` is "not in scope" rather than an unprovable goal.

One argument suffices because the receipt in context determines everything else. `give_back
w` recovers the parent, the permission, the bounds and both contents by unification
(F80) — so the surface asks the author only for the thing C# cannot tell the translator,
which is *where*.

Getting it wrong fails, and fails locally. Omit the restore and the parent's `pts_to` is
missing where the postcondition needs it. Write it too early and the window's own `pts_to`
is gone at its next use. Both land in the author's annotations, which §0 rule 3 says is
where a proof is fixed. Neither can make a false postcondition provable: the restore is a
library operation with its own precondition, not a translator assumption.

**R17.8 — what the parent holds afterwards is `Pal.Splice`.** After a window over
`[from, to)` is restored, the parent's contents are its old contents with that range
replaced by the window's: `CS.splice (old, from, to, window)` in
`Pulse.Lib.CSharp.Seq`, written `Pal.Splice(Old(Contents(a)), from, to, Contents(a))` in a
contract. `splice` is defined **total**, falling back to the parent when the indices do not
fit, so it can appear in a specification without dragging a refinement along; `splice_index`
and `splice_length` carry `[SMTPat]`, which is what discharges the usual "the window is
zero, everything outside it is untouched" postcondition without a single lemma call.

A read-only window restored unwritten gives the parent back exactly what it had, which is
`splice_same`. So a read-only borrow costs its user nothing beyond the bounds — see
`ReadAt` in `test/array_view`, whose `Contents(a) == Old(Contents(a))` needs no help.

### 17.4 What is refused

**R17.7 — the forms that are not borrows (`PALCS0590`).** The list is short now and every
entry is on it for a reason of its own, not because a rule ran out:

* **`stackalloc`.** An allocation, not a borrow: no `T[]` owns the memory, so there is no
  parent to consume and nothing for `Pal.Restore` to give back. It would need a
  scoped-lifetime allocation rule, interacting with F75's rule about `let mut` and tail
  position.
* **A range on an *array*.** `a[1..3]` where `a` is `int[]` *copies* — C# compiles it to
  `RuntimeHelpers.GetSubArray`, producing a fresh array whose writes are invisible in `a`.
  Translating it as a window would be translating a different program. The refusal is not a
  limitation but a correction, and the diagnostic says so.
* **`^k` in a range.** The from-end index is `s.Length - k`, which is ordinary arithmetic —
  but arithmetic `System.Index`'s conversion performs and the source does not write. §0's
  rule against inventing steps covers arithmetic as much as proofs; supporting it means a
  rule saying what `^k` elaborates to.
* **The implicit `T[]` → `Span<T>` conversion anywhere but a local's initializer.**
  `Wipe(a)` would borrow `a` and hand back a receipt with no name, leaving the array
  unrecoverable and failing far from the cause. The fix is one line the author can see:
  name the borrow, pass the name, restore it. (A Normalize-pass rewrite to
  `Span<T> t = a; Wipe(t); Pal.Restore(t);` would be a legitimate R2-style desugaring and is
  deferred, not rejected.)
* **`Pal.Restore` of a span *parameter*.** A restore returns a window to whoever lent it,
  and R17.6 reads which operation that is off the borrow that created the window. A
  parameter was borrowed in another method, whose receipt this one does not hold.
* **A span local assigned after its declaration.** Not a special case: a span local is bound
  with `let`, not `let mut`, so R7's general assignment rule refuses it. R17.6's origin is a
  property of the initializer, and an assignment would make "which borrow is this" depend on
  the path taken — the borrow checker §17 exists to avoid. A second window gets a second
  name.
* **`CopyTo`, `Fill`, `ToArray`, and `string`'s implicit `ReadOnlySpan<char>`.** Library
  operations with no rule yet; `Span.copy_to` exists in the library for the first of them
  and only the surface is missing.

### 17.5 What §17 does not reach

* **An inline quantified invariant over a span**, per R17.6a: C# forbids a `ref struct`
  inside a lambda (CS9108), so a *statement-position* `Pal.Forall` that mentions a span
  does not compile. Contracts are unaffected (the shim sees an array), and the idiom inside
  a loop is a named `[Spec]` predicate over the `Seq<T>`, which moves `Pal.Contents(s)` out
  of the lambda into ordinary argument position — `test/array_view` uses it in both the
  acceptance file and the variant. Nothing can be done about this from inside the scheme:
  it is a rule of the language the annotated program must keep compiling in.
* **A span-typed return.** A method may take a window and may create one, but may not hand
  one back to its caller: the receipt would have to travel with it, and R17.6 has no way to
  name a borrow the caller did not take. C# itself restricts `ref struct` returns for a
  related reason.
* **A span-typed field**, which C# forbids outright (`Span<T>` is a `ref struct`), so this
  costs nothing.
* **`Memory<T>`, `ArraySegment<T>`, `IEnumerable<T>`.** `ArraySegment<T>` is now expressible
  as a window and is a surface question only; `examples/adler32` still spells its segment out
  as three parameters and no longer has to.
* **The refused forms of R17.7**, each for its own stated reason.

---

## 18. Totality: nothing is dropped, nothing is guessed

Every rule up to here says what some C# construct *becomes*. This section says what
happens to a construct no rule mentions, and it exists because the honest answer, for a
long time, was "nothing, quietly".

The frontend collects by **positive match**. It walks a class's members looking for a
field, an auto-property, a `[Model]`, a `[Spec]` observation, a method; it walks a call
looking for a callee it can name; it walks a binary operator looking for the module that
implements it. Each of those walks ended in a fallthrough — `continue`, or a default — and
a fallthrough is a decision. It decides that a construct the rules do not cover should be
translated as though it were not there.

That is the worst of the three possible answers. A refusal tells the author what the tool
cannot do. A wrong translation is caught by F\*. But a *silent* drop reports
`0 error(s)`, emits a module that looks right, and verifies — proving a theorem about a
program the author did not write. §0 rule 3 forbids inventing a refusal; it does not
license inventing an omission.

A *silent mistranslation* is the same failure one step further along. R9.12b is the
example: a virtual method that both mutates its receiver and returns a value emitted a
dispatching wrapper that declared a return type and dropped the value, so `palcs` reported
`0 error(s)` and wrote Pulse that does not typecheck. It is less dangerous than a silent
drop — F\* rejects it, so no false theorem is proved — but it fails in the wrong place and
in the wrong language. The author asked about C# and is shown an F\* type error inside a
wrapper they did not write and cannot read, at a line number that means nothing to them.

The two have a common cause worth naming, because it is the thing to look for rather than
the thing to fix. Both arise where the emitter *branches*, and both were introduced by
adding code inside a branch that had no business being there. A `moves ? … : …` split
exists to decide how the receiver's invariant is threaded; whether a call produces a value
is an independent question, and R9.12b's defect is that the value-binding was written into
one arm of that split at three separate sites, by three separate people-shaped events, none
of which noticed. **When the same two-armed test recurs, whatever is common to the arms
should be lifted out of it rather than duplicated into it** — not for tidiness, but because
duplicating it is how one copy comes to differ from another.

### 18.1 The two rules

**R18.1 — A construct the frontend does not recognise is refused, not skipped.** Every
positive-match walk is **total**: each case either matches a category the rules name, or
raises a diagnostic that says which construct was not translated and why. There is no
fallthrough that means "ignore this".

This is one rule with five sites, and it is stated once because the five are the same
mistake:

| Walk | The fallthrough that was a decision | Now |
|---|---|---|
| a translated class's members (§3.4, §4.5) | a member matching no category was skipped, so a computed property, an indexer, a `const` field, an operator or an explicit interface implementation vanished | **PALCS0591** names the member and its kind. The computed property has since been *translated* rather than refused — that is R9.20, and it is what R18.1 is for: the report is what turns a silent gap into a named one, and a named one into a feature |
| a call's callee (R4.4) | `KindOf` accepted **any** static ordinary method, including one declared in the BCL, and emitted a call into a module that is never generated | **PALCS0592**: a callee must be declared in this compilation |
| a binary operator's operand type (R6.4) | the module was chosen by the operand's primitive kind, defaulting to `Int32` when the operand was not primitive, so `a == b` on two objects emitted `I32.eq` applied to two boxes | **PALCS0593**: an operator whose operands are not primitive has no module |
| a class's base list (R9.1) | only `BaseType` was inspected, and an interface is not a `BaseType` in Roslyn, so `class C : IFoo` silently forgot `IFoo` | **PALCS0594** until §9 has interfaces |
| a method body's receiver bracket (R4.10) | the `unfold`/`fold` bracket was opened for every instance method, so a body that only called another method on `this` handed it a representation where its contract demands the invariant | **R4.10c**: open it only when a field is named, and **PALCS0597** when a body wants both |
| a class's field declarations (R9.4) | only the declared type and name were read, so an initialiser -- an assignment R4.12 had no statement position for -- was dropped, and the field appeared to be built solely by the constructor | **PALCS0596**, and then R4.12d, which supplied the missing statement position -- the head of every constructor that does not chain -- at which point the diagnostic had nothing left to report and was retired |

**R18.2 — Every name the emitter writes is a name that resolves.** A generated module may
refer to another generated module, to a module of `Pulse.Lib.CSharp.*` or the F\* standard
library, or to a Pulse file the user supplied (§12); to nothing else. This is not a rule
the emitter can be trusted to keep by inspection, so it is **mechanically checked**:
`test/module-refs.sh` reads every qualified reference in every generated file and requires
it to resolve. It is the third detector, beside §7.2's two, and it is the one that catches
a *dangling* emission rather than an invented or an ill-provenanced one.

Two live defects were what earned it. `override int GetHashCode()` on a class with no user
base emitted `Class_Object.class_Object__model`, because the override's base was read off
`BaseType.Name` and every C# class's implicit base is `System.Object`; and
`ReferenceEquals(a, b)` emitted `Func_Object_ReferenceEquals.func_Object_ReferenceEquals`.
Neither module has ever existed. Both programs translated with `0 error(s)`.

**R18.3 — A name is emitted for at most one declaration.** R2.1's qualification by
declaring type keeps method names injective, but a constructor's name is `_ctor`
regardless of its signature, so two constructors of one class collide. Two declarations
competing for one module is not a translation, and until constructors have a
signature-bearing name, a class with more than one constructor is **PALCS0501**, the
existing module-name collision, reported with constructor-specific advice — C# does not
permit "rename one".

R18.3 was already implemented and already firing; the program still crashed with an
unhandled `ArgumentException`, because the emitter runs *despite* errors (§2 poisons the
output through `TranslationErrors.fst`) and diagnostics are printed only after it. The
throw pre-empted every message. So the fix was to make the emitter's dictionaries
collision-proof, not to add a rule: **a diagnostic that a crash outruns is not a
diagnostic**, and any pass that runs after an error must be total in the presence of one.

### 18.2 What is refused, and what each refusal is waiting for

R18.1 turns a silent drop into a diagnostic; it does not by itself translate anything new.
Each of the following is now refused *and* named as a scheme gap, which is the state a
feature has to reach before it can be designed.

* **A property with a `set` accessor, and an indexer** (PALCS0591). The *getter* half of
  this bullet is closed: R9.20 translates a computed property as the method its getter is,
  which was the largest thing R18.1 uncovered and is now the smallest feature in §9,
  because a getter *is* a method of no arguments and needed no new rule beyond finding it.
  A setter is a method of one argument whose name C# chooses, so R9.20b keeps refusing it
  until §4 has a reading of `value` in a specification. An indexer is a property with
  parameters and waits on the same.
* **A `const` field** (PALCS0591). It is a pure value and owns nothing, so it wants no
  invariant; what it wants is to be in scope in a body and in a contract, which is a
  question about §2's module layout rather than about ownership.
* **An explicit interface implementation, an operator, a conversion, an event, a
  finalizer** (PALCS0591). None has a rule, and the first two wait on §9's interfaces.
* **An `override` of a member of `object`** — `GetHashCode`, `Equals`, `ToString`
  (PALCS0591). R9.6 reads an override as the forgetting function of a *translated* base.
  `System.Object` is not translated and has no model, so an override of one of its members
  is not a forgetting function and has no other reading.
* **A call to a method not declared in this compilation** (PALCS0592). This is what makes
  `ReferenceEquals` a diagnostic. It also states, for the first time, the rule the whole
  scheme has assumed: pal-csharp translates a *whole program*, and a method whose body it
  cannot see has no contract it can trust.
* **`==`, `!=` and `ReferenceEquals` on class-typed operands** (PALCS0593, and
  PALCS0592 for `ReferenceEquals`, which is also not declared here).
  Object identity has no story: `Box` has a decidable equality, but nothing relates it to
  the ownership discipline, and two references that are equal are not thereby
  interchangeable in a context that owns one of them.
* **Two members of one program that mangle to one module name** (PALCS0501), per R18.3.
  R2.1a closed the case that motivated this bullet -- a second constructor -- by giving an
  overload set a signature suffix. What is left is a collision R2.1 admits it does not
  resolve: `Alpha.Meter.Read` and `Beta.Meter.Read` are not an overload set, because they
  are not members of one type, and the module name carries no namespace.
* **An `interface` declaration, and an implements clause** (PALCS0594). §8.6 records why
  interfaces are not simply R9.2 plus R9.3: what a C# interface adds is *multiple*
  implementation, and R9.8 pins the obstacle — a `dyn` is made at one witness type and
  `mkdyn` is not injective, so one value cannot be viewed at two unrelated roots.
* **A body that both reads a field of its receiver and calls a method on it** (PALCS0597).
  Not a dropped construct but the same mistake one level down: the bracket was emitted
  unconditionally, so the ill-typed case was emitted too. R4.10c says why the two halves
  cannot be reconciled without the emitter inventing a fold.
  R22.15 has since reconciled them for an object, with a fold that F\* checks; the
  refusal remains for a view.
* **A `record`** (PALCS0530). A record's primary constructor, its generated `Equals`,
  `GetHashCode`, `ToString` and `Deconstruct`, and its `with` expression are five features
  at once. An *annotated* record now says so; an unannotated one is ignored, like any
  unannotated type — R18.1 governs what the translator was asked to translate, not every
  declaration in the compilation. PALCS0530 previously read "does not translate classes
  yet", a message left over from before §3.4 was built and untrue as stated.

* **What §19 does not yet translate** (PALCS0610–PALCS0615): an exception class that is
  generic or derives from a library exception other than `System.Exception`; a payload
  member that is settable or is not a value; more than one constructor, or one that
  computes; `finally`; a `return`, `break` or `continue` that leaves a `try`; a `try` while
  a receiver's representation is open; and a handler for a type that is not an exception
  class of the program. Each is listed in §19 with what it waits on.

### 18.3 Why this is a section and not a bug list

Everything above could have been fixed one `if` at a time. It is written down as a rule
because the four sites are one mistake made four times, and because the mistake is
*structural*: a compiler assembled from positive matches drops what it does not match, and
will do so again at the fifth site unless the rule is that a walk must be total.

That also fixes what the refusals mean. §0 rule 3 says the frontend refuses what it cannot
*translate*, never what it predicts will not *prove*. Every diagnostic in §18 is the first
kind, and each names a construct with no image under any rule in this document — which is
also why each is listed in §18.2 with the rule that would have to exist for it to be
accepted.

---

## 19. Exceptions

C#'s `throw` and `try`/`catch` are translated to the native exceptions of Pulse
(FStarLang/FStar#4798): `raise`, `try … catch`, and a `raises` clause on a `fn` that says
what holds when it raises. The translation is three rules about values and two about
control.

### R19.1 An exception class is an F* `exception` and a discriminator

Every exception class of the program is declared in one module, `Exceptions`, because a
class's discriminator has to name the F\* exception of each of its subclasses. For a class
`E` with fields `F₁ … Fₙ` (inherited ones first):

* if `E` is concrete, `noeq type exn_E__payload = { exn_E__p_F₁: τ₁; … }` and
  `exception Exn_E of exn_E__payload` (or `exception Exn_E` with no fields). Field names are
  prefixed by the class so that two payload records never share a field name;
* `exn_E__is : exn -> bool` matches `Exn_D` for every concrete `D` that is `E` or derives
  from it, and `type exn_E = e:exn{exn_E__is e}` is the image of the C# type `E`.
  `System.Exception` is `exn`;
* `exn_E__fld_Fᵢ : exn_E -> τᵢ` reads the field through whichever subclass was thrown. The
  match is exhaustive because of the refinement;
* `exn_E__new`, for a concrete class, is its constructor, which the frontend reads as a
  pure function from its parameters to the payload.

That is all of C#'s subtyping on exceptions: a handler for `B` catches a `D : B` because
`exn_B__is` holds of it, and `e.Code` on a `B` is the accessor's `D` case.

The payload is immutable, which is what C# programs overwhelmingly write: an exception
class may have get-only auto-properties and readonly fields of value type (PALCS0611); at
most one constructor (PALCS0612), which may only call `base(…)` with its parameters or
literals and assign its own fields from them (PALCS0613); and it may derive only from
`System.Exception` or from another exception class of the program (PALCS0610), since a
library base's fields would be payload the translator cannot see. `Message` and
`InnerException` are not modelled: arguments passed to `System.Exception`'s constructor
must be parameters or literals, and are not evaluated.

### R19.2 `throw` is `raise`

`throw e;` is `let t = ⟦e⟧; raise t`. `raise` has every type, so a throw is a statement, a
branch's value or a method's tail alike (F87). Before the `raise`, an object the method
holds is closed exactly as before a `return` (R4.10, R4.14): the `raises` clause owns it
folded, as the postcondition does. Inside a `try`, only object locals the `try` itself
declared are dropped, since the `try`'s own `raises` owns the rest. `throw;` re-raises the
innermost handler's exception.

### R19.3 `[Throws]` is the `raises` clause

`[Throws(typeof(E), "P")]` says the method may throw an `E` (or a subclass), and that `P`
holds when it does. `P` is a specification over the parameters' *pre-state* values and
`Thrown`, which denotes the exception at type `E`. Several `[Throws]` are a disjunction.
The emitted clause is

    raises (fun (thrown: exn) ->
      exists* <post-state binders>. <every parameter's resource, as in the postcondition> **
      pure (PRE ==> (exn_E₁__is thrown /\ ⟦P₁⟧) \/ …))

It owns what an exception leaves the caller owning: each parameter, and nothing the
method would have returned. Like R4.8's `ensures`, it is stated under the precondition. A
method with no `[Throws]` has no `raises`, so Pulse makes it prove that it raises nothing
(F87).

`P` is stated over pre-state values, not post-state ones, so that the same text is
meaningful inside a `try` (R19.4), where there is no post-state to speak of.

### R19.4 `try`/`catch` is Pulse's `try`

    try
      ensures  exists* <assigned>. <live resources> ** pure (INV)
      raises (fun ex -> exists* <assigned>. <live resources> **
                        pure (INV /\ (exn_E₁__is ex \/ … \/ ENCLOSING ex)))
    { body }
    catch { ex -> { let var_e = ex; if (exn_E₁__is ex && ⟦when₁⟧) { h₁ } else … else { raise ex } } }

* **Ownership.** A `try` is not framed (F86), so its clauses own every slot live across it,
  assembled exactly as a loop invariant's are (R5.8b): a slot the `try` does not assign is
  held at the value it had, one it does is existentially quantified, and R5.10's escape
  flags of an enclosing loop are carried too.
* **What reaches the handler.** The `raises` says the exception is one some unfiltered
  clause handles (`catch (E)` contributes `exn_E__is ex`, `catch (Exception)` contributes
  `True`), or one the enclosing construct may raise: the method's `[Throws]` (R19.3) or
  an outer `try`'s `raises`. This is exactly what proves the handler's closing
  `raise ex`. A `when` filter does not contribute, because a filtered clause may decline.
* **The handler.** Clauses are tested in order. A clause's variable is bound to the
  exception, and its filter is evaluated under that binding with `&&` guarding the class
  test, so a field read in the filter is well typed. A filter must be pure (PALCS0614).
* **What a handler knows.** It knows the class of what it caught and nothing more (F87):
  a callee's `[Throws]` predicate is not carried into the `try`'s `raises`. A handler
  must test the fields it relies on, and a rethrow can promise only what the `try`'s
  `raises` says. `test/throw_catch` has both cases, and in both the verifier found the
  overflow and the negative index a trusting handler would have had.

Refused (PALCS0614): `finally`, which runs on every exit and has no Pulse counterpart; a
`return` anywhere in a `try`, and a `break` or `continue` that leaves one, since the `try`'s
`ensures` describes only its fall-through exit (assign a local and return after the
`try`); and a `try` while a receiver's representation is open (R4.10) or inside a null
test's window (R10.7), which the `try` would have to carry across both exits. Handlers
for anything but `System.Exception` and the program's exception classes are refused
there too, and a `[Throws]` naming a non-exception type is PALCS0615.

### R19.5 A `try` invariant

The value facts about a slot the `try` assigns would be lost by R19.4's existentials. A
try states them the way a loop does: `Pal.Invariant(INV)` at the head of the `try` body.
`INV` must hold wherever control leaves the body, at its end and at every raise that
reaches the handler, and at the end of every handler. It is stated over the slots' values
at that point, and it is what a statement after the `try` may rely on. A
`Pal.Decreases` there is refused (PALCS0614): a `try` runs once.

---

## 20. Verifying production code in place

§§1–19 translate a program written for pal-csharp. This section is about the other case:
a production file, written for a product, which is to be verified as it stands, by adding
attributes to it and nothing else. `~/Verified-CPQ-Components/tier-schedule` is the
motivating case, a Dataverse plugin of which one method is verified. Such a file uses
library types the earlier sections refuse (`decimal`, `string`, `T?`, `IList<T>`, LINQ,
delegates) and is mostly code nobody means to verify. The rules below admit exactly what
that needs, each pinned by a hand-written probe first (§0), and each library model is a
MODELING AXIOM that is listed under R20.8.

### R20.1 `[assembly: TranslateAnnotatedOnly]`

Under this attribute only *annotated* code is translated: a method that carries a
pal-csharp attribute (`[Requires]`, `[Ensures]`, `[Throws]`, `[Admit]`, …), or is the
getter of a property that does, or belongs to a class with a model; and a struct that, or
one of whose members, carries one. Everything else in the compilation is ignored: it is
not lowered, and the "specified class without a model" diagnostic (PALCS0524) is not
raised (R22.3: a class with a model is likewise verified member by member). A call from translated code to an
untranslated method is still refused, as before, so the scope narrows what is *looked at*
and never what is *trusted*.

**R20.1a (receiver-free instance methods).** In that scope an annotated instance method
of a class with no model is translated as a static function when it does not touch
`this`: a production class's private helper (`ValidateBandSchedule`) usually reads only
its parameters, and the class around it (a plugin strategy, holding services) has no
meaning in Pulse. A read of the receiver's state is refused, like any other read of an
untranslated object (R18.1).

**R20.1b (exception classes out of reach).** In that scope a user exception class whose
payload does not translate (it carries a `DateOnly`, a list, an object) is not refused:
like any class the annotations do not reach, it is left untranslated, and a `throw` of it
in translated code is refused there.

**Harness variables.** `test/verify.mk` reads `PAL_CS_NULLABLE` (R20.9),
`EXTRA_INCLUDES` (directories of F\* sources a harness's model lives in, added to
`--include`) and `EXTRA_CACHED` (a comma-separated list of those modules, added to
`--already_cached`, since they are checked by the model's own build). The file re-invokes
itself, so a harness Makefile `export`s them.

### R20.2 `[Admit]` bodies are not lowered

The body of an `[Admit]` method is never read: its contract is assumed (PALCS0900), so
nothing in the body (a localised-message lookup, say) needs to be translatable.

### R20.3 Library value types

| C# | Pulse | Operations |
|---|---|---|
| `decimal` | `D.decimal` (`Pulse.Lib.CSharp.Decimal`) | literals `D.lit`; `==`/`!=` as `=`; `<` `<=` `>` `>=` as `D.lt` … `D.ge`, refined by the order on `D.v : decimal -> real` |
| `string` | `string` | literals; `==`/`!=` |
| `T?` (`Nullable<T>`) | `option ⟦T⟧` | `HasValue` ⟶ `Some?`; `Value` ⟶ `Some?.v` (well typed only under `HasValue`, which F\* checks); `null` ⟶ `None`; the implicit `T → T?` ⟶ `Some` |
| a delegate type | `Opaque.delegate "D"` | a method group `C.M` ⟶ `Opaque.method_group "C.M"`; nothing else |

Any other operator on `decimal` or `string` (arithmetic, concatenation, interpolation) is
PALCS0624. A delegate value has no behaviour: it can be passed to an `[Admit]` method, and
that is all; invoking one is refused.

### R20.4 `IList<T>`, `IReadOnlyList<T>`, `List<T>` are arrays

A list-like type is translated exactly as `T[]` (R6): a parameter is
`A.pts_to a #p s`, `.Count` is `length_i32`, the indexer is `read`, and
`Pal.Contents(list)` is its `Seq`. Parameter permissions follow the array rules, so
`[Frac("p")]` makes a list parameter read-only.

### R20.5 `foreach` over an array or list, and `Pal.Index`

`foreach (var x in c) { INV; body }` is translated as the counted loop

    for (int x__index = 0; x__index < c.Length; x__index++)
    { Invariant(0 <= x__index && x__index <= Contents(c).Length); INV; var x = c[x__index]; body }

so R5's loop rules apply, with the measure that R5's counter inference finds. Inside `INV`,
`Pal.Index(x)` names the position of the current element, `x__index`. `c` must be a local
or a parameter of array or list type that the body does not assign (PALCS0620), and
`Pal.Index` must be applied to a `foreach` variable in scope (PALCS0621).

### R20.6 `OrderBy(…).ToList()`

`src.OrderBy(x => x.P).ToList()`, with `P` a `[SpecOp]` property of `decimal` or a machine
integer type, is

    let t = Linq.order_by_to_list ⟦src⟧ ⟦P⟧ ⟦≤⟧

whose result owns a fresh array with contents `Linq.sort_by ⟦P⟧ ⟦≤⟧ s`. `sort_by` is a
stable insertion sort, defined and proved in F\*; only `order_by_to_list`'s body, the link
between it and the CLR's `OrderBy`, is assumed. Any other LINQ is PALCS0622.

**R6.11a (array-owning locals).** A local initialised with `new T[n]` (R6.11) or with
R20.6's `ToList` owns its array. Its declaration is `let var_x = …` (no reference cell),
and it is dropped, like an object local (R4.14), at every `return` and `raise` and at the
end of the method. It must be declared in the method's outermost block (or moved into a
field before its block closes, R22.17) and not be reassigned (PALCS0623), so that a single drop point covers every exit.

### R20.7 `[SpecOp]` members in code

A `[SpecOp]` property or method read in *code* is a pure application of the F\* function
it names. This is what makes a `[SpecType]` class a value type to the translator, and it
is sound only under R20.8's assumption that the object is not mutated.

* A generic `[SpecOp]` method with a type parameter that no parameter type mentions,
  `e.Get<T>(k)`, passes its type arguments first, as R14.2 does:
  `M.get (option I32.t) ⟦e⟧ ⟦k⟧`. When every type parameter occurs in a parameter type,
  the F\* function binds it implicitly and F\* infers it from the arguments. A `[SpecType]` may be an interface.
* An indexer whose `get` carries a `[SpecOp]` is read as that operation applied to the
  receiver and the index.
* A constructor with a `[SpecOp]`, `new C(a, b)`, is `M.f ⟦a⟧ ⟦b⟧`; with an object
  initializer it is refused. A user-defined *implicit* conversion with a `[SpecOp]` is
  applied where C# applies it, ahead of R20.3's `Some`.
* `x == null` on a `Nullable = true` value is `None? x`, and `x != null` is `Some? x`.

### R20.9 Code written before nullable reference types

`palcs --nullable disable` (`PAL_CS_NULLABLE=disable` in a test or harness Makefile)
compiles the sources with nullable reference types off, as pre-C# 8 production code is.

* An *oblivious* `string` — one declared where nullable annotations are disabled — may be
  null, and is `option string`. A string constant where one is expected is `Some "…"`.
  Under `#nullable enable` a `string` stays `string` (R3.1).
* `(int)E.M`, a cast of an enum constant, is the integer C# folds it to: enums are not a
  type the translation models, but each of their constants is a literal.
* `==` and `!=` on an `option` or a `[SpecType]` value is F\*'s decidable equality `=`;
  `x == null` compares with the `None` of `x`'s type.

### R20.10 The BCL members with a model

`Pulse.Lib.CSharp.Bcl` models the few BCL members validation code calls, each as the
function it is:

| C# | F\* |
|---|---|
| `Guid`, `Guid.Empty` | `Bcl.guid` (an `eqtype`), `Bcl.guid_empty` |
| `string.IsNullOrWhiteSpace(s)` | `Bcl.is_null_or_white_space s` |
| `string.Equals(a, b, StringComparison.Ordinal)` | `Bcl.string_equals_ordinal a b` |
| `new Regex(pattern, options)` with constant arguments | `Bcl.regex_create "pattern" options` |
| `r.IsMatch(s)` | `Bcl.is_match r (Some?.v s)` — F\* proves `s` non-null |
| `new HashSet<T> { a, b }`, `h.Contains(x)` | `Bcl.hash_set_add a (… Bcl.hash_set_empty)`, `Bcl.hash_set_contains h x` |

Any other use of these members — another `StringComparison`, a non-constant pattern, a
set built any other way — is PALCS0625.

A `static readonly` field whose initialiser is such a value (built only from constants,
`Some`, `null` and model applications) denotes its initialiser, which is written out at
each use: the field is assigned once, before any method runs, and never again. Any other
`static readonly` field read by verified code is PALCS0626.

A `static readonly` initialiser is *code*: written out at a use inside a specification it
keeps its machine types (`0l`, not `0`), as do the arguments of the BCL models above,
whose F\* signatures take machine integers.

### R20.11 Nullable references: `[SpecType(…, Nullable = true)]`, `?.` and `??`

A `[SpecType("T", Nullable = true)]` class is a reference that may be null: a variable of
it is `option T` (unless `#nullable enable` marks the occurrence non-null). A `[SpecOp]`
member read through such a variable is applied to `Some?.v x`, so F\* must prove `x`
non-null where it is read — a `NullReferenceException` is ruled out, not assumed away.

`a?.M` is `let t = a in if Some? t then [Some] ⟦t.M⟧ else None`, and `a ?? b` is
`let t = a in if Some? t then Some?.v t else ⟦b⟧` (`t` itself when `b` is nullable). `a`
is evaluated once (bound to a fresh local when it has an effect), and `M` and `b` only on
the branch where C# evaluates them.

### R20.12 Context fields of a receiver-free method

A receiver-free method (R20.1a) may read the `readonly` instance fields of its class
(services, configuration the constructor stored). Each such field that an annotated
receiver-free method of the class reads, in its body or its contracts, becomes a parameter
`this__f` of *every* annotated receiver-free method of the class, and a call between them
passes it on. That is sound because a `readonly` field is assigned only by the
constructor, and the receiver is the same object throughout such a chain of calls; it is
never a `let mut` cell, since it cannot be assigned. A contract may name these fields, and
the `static readonly` fields of R20.10, though they are private: the specification shim
receives them as parameters, and a static one denotes its initialiser.

**R20.12a (captured primary-constructor parameters).** A parameter of a class's primary
constructor that a member captures and nothing assigns, `class C(IKernel kernel)`, holds
the constructor's argument for the object's lifetime, exactly as a `readonly` field does,
and is a context value like one: a parameter `this__kernel` of every annotated
receiver-free method of the class.

### R20.13 An SDK object written through its indexer

A by-value `[SpecType]` parameter `x` that the method writes through an indexer whose
`set` carries a `[SpecOp]` — `x[k] = v` — or passes to a parameter that is written, is
passed by reference: `x[k] = v` is `x := M.put (Some?.v x) ⟦k⟧ ⟦v⟧` (`Some?.v` when `x` is
nullable, with F\* proving it non-null), its pre- and post-values are `Old(x)` and `x` in
`[Ensures]`, and an argument to such a parameter must be a local or a parameter (PALCS0001
otherwise). This models the write a caller observes on the shared object — the model is a
value, so R20.8's "no mutation through an alias" becomes "no mutation except through the
parameters R20.13 finds". `Pal.Same(a, b)` states equality where `==` is not decidable
(a model holding a function).

### R20.8 What a proof of production code trusts

* the decimal model: `decimal` is an `eqtype` injected into `real` by `D.v`, and the C#
  comparisons agree with the order on `real`;
* LINQ: `OrderBy` is stable and `ToList` copies its source in order;
* `IList<T>`: the implementation honours its contract (`Count` agrees with the indexer,
  `foreach` enumerates in index order and the list is not modified during it);
* a `[SpecType]` class read through `[SpecOp]`s: its elements are non-null and are not
  mutated through an alias while the verified method runs;
* the BCL models of R20.10: `Guid` equality, `IsNullOrWhiteSpace` (with `char.IsWhiteSpace`
  uninterpreted), ordinal `string.Equals`, `HashSet` membership, and that `Regex.IsMatch`
  is a deterministic, terminating function of the pattern, options and input;
* an SDK object modelled as a value (R20.13): it changes only through the indexer writes
  of the method under verification, and a generic read (`GetAttributeValue<T>`) returns
  a value of the type it is read at (the cast failure the SDK throws otherwise is not
  modelled);
* the `readonly` fields of R20.12: the receiver of a chain of receiver-free calls is one
  object, and a `[SpecType]` value in such a field (a `HashSet`, a model) is not mutated;
* the bindings of R21.5: each `[SpecBinding]` is an axiom that the library member
  computes the F\* term it is bound to;
* a `[SpecType]` enum (R21.8): every value of it a program sees is one of its declared
  constants (no `(E)42`);
* a closed hierarchy (R21.1): no case beyond the sealed records the compilation declares,
  and the validation a record's constructor performs is not modelled (construction is
  total);
* the BCL exceptions of R21.7 are distinguished by type only: their messages are not
  modelled;
* every `[Admit]`ed contract, and whatever stand-ins the harness supplies for types
  outside the file.

## 21. Closed record hierarchies, enums, patterns and library bindings

Production C# written in a functional style -- a value domain as an `abstract record`
with `sealed record` cases, dispatch by `switch` expressions and `is` patterns, enums as
tags, `throw` in expression position -- maps onto an F\* inductive and `match`, which is
how the F\* model of such code is usually written. `~/Verified-CPQ-Components/dmn-feel`,
whose `Feel.Core` evaluator is verified in place against the `Feel.Semantics` model, is
the motivating case; `test/record_cases` pins each rule.

### R21.1 A closed hierarchy is an inductive

An `abstract record B` carrying `[SpecType("M.t")]` (with `Nullable = true` when a `B`
variable may be null, R20.11) whose cases are the `sealed record`s deriving from it is the
F\* inductive `M.t`. A case `C` is the data constructor `[SpecCase("M.K")]` names, or `M.C`
by default; `new C(a, b)` is `M.C ⟦a⟧ ⟦b⟧` with the arguments in the order of `C`'s one
constructor. A case is not a separate type in F\*: a variable of type `C` is an `M.t`, and
`C`'s image of a test is `M.C? x`.

### R21.2 Components

A positional property of a case, `c.P`, is the projection
`(fun (x:M.t{M.C? x}) -> match x with | M.C .. v .. -> v) ⟦c⟧`, so F\* proves `c` is a `C`
where it is read -- which C#'s static type of `c` guarantees, and the narrowing of R21.3
supplies.

### R21.3 Patterns

`e is P` is a boolean, and the variables `P` binds are in scope where C# says they are
definitely assigned, each the expression it was bound to (so no `let mut` cell, and F\*
sees the same term the test was about). The subject is evaluated once: an expression with
an effect is bound to a fresh local first.

* A type pattern `C c` is `Some? x && M.C? (Some?.v x)` (the `Some?` only when the subject
  is nullable), binding `c` to the narrowed value; a type that is not a case of the
  subject's hierarchy, nor its own type, is PALCS0627. A constant pattern that names a type
  (`case B.C =>`) is the same test.
* A property pattern `{ P: p, Q: 3 }` and a positional pattern `(p, 3)` test and bind
  components (R21.2); `var x` and `_` always match; `not`, `and`, `or`, relational
  patterns (`< 3`) and constants are their boolean images.
* `null` tests `None?`, and `not null` `Some?`.

### R21.4 `switch` expressions

A switch expression is a chain of conditionals, one per arm in order, each the pattern's
test conjoined with its `when` clause; the last falls through to a raise of C#'s
`SwitchExpressionException` (R21.7), which F\* must prove unreachable unless the method
`[Throws]` it. When the switch's type is an `option`, an arm whose value is not one is
`Some` of it (Roslyn reports a target-typed switch's conversion on the switch, not the arms).

When one branch of a conditional emits statements and the other is a bare term, the term
is let-bound in its branch: Pulse's join of the two branches otherwise lost the facts the
statement branch established (F89).

### R21.5 Library bindings: `[assembly: SpecBinding(id, term)]`

A library member the program cannot annotate is bound by documentation-comment ID:
`"T:System.DateOnly"` to an F\* type, and `"M:…"`/`"P:…"`/`"F:…"` -- methods, operators
(`op_LessThan`), properties and static fields -- to an F\* function or constant, applied
like a `[SpecOp]` (R11.2). A user-defined operator so bound is an application wherever C#
calls it. Each binding is an axiom (R20.8).

### R21.6 `as` and pattern variables

`e as C` is `if ⟦e is C⟧ then Some e else None`. A pattern variable has the type of the
value it was bound to: `var` declares it nullable whatever it matched, so the translation
uses the bound value's type rather than the declared one.

### R21.7 `throw` in expression position; BCL exceptions

`throw e` in a switch arm or a conditional branch is a raise at the type of its context:
`raise e; let _ = elim_pure_explicit False; false_elim #(T) ()`. Pulse types a raise with no
expected type as `unit`, with postcondition `pure False`; the elimination turns that into
any `T` (F88).

An exception the BCL declares (`ArgumentException`, `InvalidOperationException`, …)
is `Pulse.Lib.CSharp.Exn.BclException "System.ArgumentException"`: one F\* exception
carrying the class's full name, so a `catch` of it, or `[Throws]`, distinguishes classes
but not messages. It translates when its arguments are constants (PALCS0628 otherwise).

### R21.8 Enums

An `enum` carrying `[SpecType("M.t")]` is the F\* inductive `M.t` with one nullary
constructor per constant (`[SpecCase]` renames one). A constant is its constructor, `==`
is F\* equality, and a `case E.A` pattern is `M.A? x`. An enum without the attribute keeps
the R20.9 reading: each constant is the integer it folds to.

### R21.9 Flow-narrowed nullable variables

A nullable variable that C#'s flow analysis knows is not null at a use where a non-nullable
value is expected (`if (x is null) return …; f(x)`) is `Some?.v x`: F\* proves it non-null
from the same tests C# drew the conclusion from.

### R21.10 A non-null reference written at a nullable type

Nullability of a reference type is an annotation, so C# reports no conversion when a `B`
is assigned to a `B?` local, initialises one, or is returned from a method returning `B?`;
the images differ, `M.t` and `option M.t`, and the conversion is `Some`.

### R21.11 A parameter named `result`

The postcondition's binder is `var_result`, so a C# parameter or local named `result` is
`var_result'` (R4.4).

## 22. Collections verified in place

dotnet/runtime's `System.Collections.Generic` is library code written for speed: a class
that is not `sealed` but has no subclass, a `[DoesNotReturn]` throw helper, a version
stamp that wraps, a property setter that reallocates, `Array.Copy`, `Debug.Assert`. It is
verified where it stands, as §20 verifies a plugin, with `[TranslateAnnotatedOnly]` and
contracts added to the file and nothing else. `List<T>` is the motivating case (its harness
is `pal/List` in the runtime checkout); `test/collections_foundation` pins each rule below
on a smaller list.

### R22.1 The list being verified is a class

R20.4 reads `List<T>` as an array. That reading is for a *client* of the BCL's list; in a
compilation that declares `List<T>` itself, it is translated as the class it is.

### R22.2 An enum without `[SpecType]`

is its underlying integer type, as its constants already are (R20.9): a tag that is passed
along and compared, and never matched on. R21.8 is the reading with the attribute.

### R22.3 Membership of a class is not a request

Under R20.1's scope a class with a model is verified member by member: an unannotated
member is outside the scope, not a construct to refuse, and a call to it from translated
code is refused where it is made (amending R20.1, which brought in every member of such a
class).

### R22.4 Implements clauses are ignored in scope

Under `[TranslateAnnotatedOnly]` an implements clause is not PALCS0594: no call through an
interface translates, since its members have no module, so the class is verified as itself
and an interface-typed call is refused at the call.

### R22.5 An effectively sealed class

Under `[TranslateAnnotatedOnly]` a class that is not `sealed`, but declares no virtual or
abstract member and has no subclass in the compilation, is a leaf. A subclass elsewhere
can add state, but cannot change what any of this class's methods do, so there is no
vtable for R9.21 to split off.

### R22.6 Generic `[Spec]` structs

A `[Spec]` struct may have type parameters (`ListModel<T>` with a `Seq<T>` field). They are
explicit parameters of its F\* record type and of its constructor, in declaration order.

### R22.7 `const` fields

are folded where they are read, like R20.10's `static readonly` constants.

### R22.8 A shared empty array is fresh

`private static readonly T[] s_emptyArray = new T[0]` is read, in code, as a fresh
`new T[0]`. It has no cells, so no write through one alias can be observed through the
other; reference identity, the only thing that tells them apart, has no translation
(R18.1). *Trusted*: that nothing compares the array by reference.

### R22.9 Constructors with control flow

A constructor body that is more than field initialisations runs as C# runs it: the object
is allocated with every field at its default (C# zero-initialises a field nothing
assigns), and the body is then an ordinary method body over the open representation, which
is folded into the invariant at each `return`.

### R22.10 `new T[n]` at a type parameter

fills with `default(T)`, so it needs the caller's `has_default` exactly as R14.2a's
`default(T)` does, unless the length is the literal zero. `new T[0]` is
`Pulse.Lib.CSharp.Array.alloc_empty`, whose ownership of zero cells is a MODELING AXIOM.

### R22.11 `[DoesNotReturn]` helpers

A call to a method carrying `[DoesNotReturn]` is a throw point: the caller hands back what
it holds before the call, as before a `throw` (R19), and discards the box of an object a
constructor is building, with the arrays its fields own. The callee's own contract is
`[Ensures("false")]` with its `[Throws]`.

### R22.12 Joins that would lose facts

Pulse joins the two arms of an unannotated `if` resource by resource, generalising each,
so the facts that tie an open object's fields to the arrays it owns are lost. When an arm
replaces an array field of an open object, calls a method on an open receiver (R22.15), or
copies into an array (R22.20), the `if` does not join: the statements after it are emitted
in each arm. An `if` with no `else` in tail position is split as one with an empty `else`.
An arm that never completes — it ends in a `throw`, a `return`, or a `[DoesNotReturn]`
call (R22.11) — does not receive them: behind its `unreachable ()` nothing is held. A
`[DoesNotReturn]` call in tail position makes `unreachable ()` the block's value, with no
epilogue after it.

R22.12a. A `return`, or a local initialised, with `&&`, `||` or `?:` one of whose operands
calls a method on an open receiver (R22.15) is first rewritten to the `if` it abbreviates,
so that the call is a statement and the receiver can be folded around it.

R6.3a (amended here). When both arms of a value-returning branch consist only of total
reads (`!x` of a local cell, `B.op_Bang this`), at least one of the receiver's box, the
reads are hoisted before an F\* `if`:
a Pulse `if` with a value loses the relation between its result and a read made in an arm.

### R22.13 Properties and indexers

A property's setter is the method `set_P(value)`, and an indexer's accessors are
`get_Item`/`set_Item`, as C# compiles them, each with its own contracts. The getter of a
property that also has a setter, and is not an auto-property, is collected as a method
too; an `init` accessor is not.

### R22.14 `[Wrapping]`

On an integer field, the arithmetic that writes it, and on a method, all the integer
arithmetic in its body, is two's-complement: C#'s unchecked `+`, `-` and `*`, with no
overflow obligation (`*_wrap` in `Pulse.Lib.CSharp.Int32`, `_mod` for an unsigned width).

### R22.15 A self-call with the receiver open

A method that reads a field of `this` and then calls a method on `this` (once PALCS0597)
folds its receiver before the call, so the callee is given the invariant its contract
demands, and reopens it after: by `unfold` when the callee is read-only, and otherwise by
`with m. assert (inv this m); unfold inv this m` for the model the callee left. The fold
is checked by F\*, not assumed. PALCS0597 remains for a receiver that is a view (R17).

### R22.16 Sequence builders

`Pal.Snoc(s, x)`, `Pal.Append(s, t)` and `Pal.Empty<T>()` are `Seq.snoc`, `Seq.append`
and `Seq.empty`.

### R22.17 A fresh array in a nested block

R6.11a's array-owning local may be declared in a nested block if, by the end of the block,
it has been moved into a field (R22.12); one that still owns its array there is PALCS0623.

### R22.18 `Array.MaxLength`

is the literal `0x7FFFFFC7`. It is a property only so that the runtime may change it;
*trusted*: that the runtime being verified uses that value.

### R22.19 `Debug.Assert(c)`

The translation models **Release C# without `DEBUG`**. Both `Debug.Assert` and
`Debug.Fail` are erased completely, including evaluation of conditions and messages.
Use `Pal.Assert` for a checked proof assertion. The earlier translation evaluated
`c` and asserted its result; this incorrectly executed mutations and calls absent
from the Release program. Earlier explanatory references to checked `Debug.Assert`
statements in this document describe that superseded behavior.

### R22.20 `Array.Copy(src, dst, len)`

between two distinct arrays of one element type is `Pulse.Lib.CSharp.Array.copy`, proved
from `memcpy`: the caller shows `0 <= len <= length` of both, and `dst`'s contents become
`Seq.append (Seq.slice s 0 len) (Seq.slice d len (length d))`.

### R22.21 Assigning a property or indexer

`P = v` (or `o.P = v`), for a property with a translated setter, calls `set_P(v)`. A
one-argument class indexer write `o[i] = v`, when its setter is translated, calls
`set_Item(i, v)`. A method that does either mutates its receiver.

### R22.22 `has_default` propagates

A method that calls one needing `has_default` at a type parameter (R22.10, R14.2a) needs
it too, at the type parameter the call instantiates it with; this is computed to a fixed
point over the calls.

### R22.23 Sequence equality

`==` between two sequences, one of which is built by an operation (R22.16, `Pal.SetAt`,
`Pal.Slice`), is `Seq.equal`: they agree pointwise, and the SMT pattern of
`Seq.lemma_eq_elim` turns that into equality. Between two names, `Seq.equal` would only
cost the solver a quantifier, so `==` stays. `Pal.Reverse` and `Pal.Splice` are built;
so is the contents of a returned array (R22.28), where `==` would let Pulse's prover pick
the existential from the equation and then fail to match the array the method owns.

### R22.24 What is trusted

Beyond R20.8: `alloc_empty` (R22.10), the sharing of the empty array (R22.8), the value of
`Array.MaxLength` (R22.18), `default_equals` (R22.25: that `EqualityComparer<T>.Default`
is the uninterpreted equality the model searches with) and
`is_reference_or_contains_references` (R22.26). Out-of-memory is not modelled: an allocation succeeds, so a
capacity is not proved to be at most `Array.MaxLength`.

### R22.25 Array bulk operations and searches

The `System.Array` members the collections use are modelled in
`Pulse.Lib.CSharp.Array`, each proved from Pulse's array library:

| C# | Pulse | contents afterwards |
|---|---|---|
| `Array.Copy(s, si, d, di, n)`, `s` and `d` distinct | `copy_at` | `CS.copied_at` |
| `Array.Copy(a, si, a, di, n)` (one array, by syntax) | `move` | `CS.copied_at`, of the old contents |
| `Array.Clear(a, i, n)` | `clear` (`has_default`) | `CS.cleared` |
| `Array.Reverse(a, i, n)` | `reverse` | `CS.reversed` |
| `Array.IndexOf(a, x, i, n)` | `index_of` | unchanged; returns `CS.index_of s x i n` |
| `Array.LastIndexOf(a, x, i, n)` | `last_index_of` | unchanged; returns `CS.last_index_of_at s x i n` |

The BCL's argument errors become preconditions, not `[Throws]`: the caller proves the range
is in bounds. Named arguments are matched to parameters. A search compares with
`default_equals`, so `Pal.DefaultEquals(a, b)` is available in specifications, and its
result is `-1` or an in-range index holding a match (lemmas `index_of_range`,
`last_index_of_range`, with SMT patterns). A search is not a write for R4.11b. In
specifications, `Pal.IndexOf(s, x)`, `Pal.IndexOf(s, x, i, n)`, `Pal.LastIndexOf(s, x)`,
`Pal.LastIndexOf(s, x, index, count)` and `Pal.Reverse(s)` denote these functions, and
`Pal.Slice`/`Pal.Splice` take `SpecInt` indices so that `Pal.Old(...)` may be passed.

### R22.26 `RuntimeHelpers.IsReferenceOrContainsReferences<T>()`

is the uninterpreted `is_reference_or_contains_references ty_T` (trusted, R22.24): it only
decides whether the runtime clears storage, and either answer is safe in the model.

### R22.27 `checked(e)`

is `e` with R5.3's no-overflow obligation, even inside a `[Wrapping]` method: an
`OverflowException` is proved never to be thrown rather than modelled.

### R22.28 Returning an array

A method whose return type is an array returns it owned: the postcondition holds
`A.pts_to result s` for an existential `s`, and `Result`/`Pal.Contents(Result)` in the
contract denote `s`. A returned array local is not re-bound before the epilogue (as R4.12
for an object), so Pulse's matcher sees it by name.

### R22.29 Expression-bodied members

An `=>` body is lowered as code, as the block `{ return e; }` (or `{ e; }` for a void
member, `{ throw … }` for a throw expression), so that code-only forms such as R22.25's
searches are available in it.

### R22.30 Comparers

`Pulse.Lib.CSharp.Order` (trusted, R22.24) models a comparer as a ghost value of type
`comparer t`, with `default_comparer t` for `Comparer<T>.Default` and `compare c x y`
for `c.Compare(x, y)`, up to sign. A comparer is assumed to be a deterministic total
preorder: `compare_refl`, `compare_antisym` and `compare_trans`. How a collection's
contract names its comparer, and how a call to `Compare` lowers, is given with the
collection families that use it.


### R22.31 `[Rlimit(n)]`

On a method, its module is checked with `#set-options "--z3rlimit_factor n"`: the solver
may take `n` times as long. Nothing about what is proved changes.

## 23. Queue, Stack and LinkedList

The array-backed `Stack<T>` and `Queue<T>` of dotnet/runtime are verified in place with
§22's machinery; the rules below are what they needed in addition. Library support is in
`Pulse.Lib.CSharp.QueueStack` (proved; nothing assumed) and `Pulse.Lib.CSharp.Seq`.
`test/collections_queuestack` exercises each rule.

### R23.1 `Array.Empty<T>()`

is a fresh array of length 0, as `new T[0]` (and trusted in the same way as R22.8: the
CLR shares one instance per `T`, and a zero-length array has no cells to alias).

### R23.2 Argument guards

`ArgumentOutOfRangeException.ThrowIfNegative(x)`, `ThrowIfNegativeOrZero`, `ThrowIfZero`,
`ThrowIfLessThan(x, y)`, `ThrowIfLessThanOrEqual`, `ThrowIfGreaterThan`,
`ThrowIfGreaterThanOrEqual`, `ThrowIfEqual` and `ThrowIfNotEqual`, at an integral type, are
the `if (cmp) throw new ArgumentOutOfRangeException(...)` they abbreviate, so the
contract states the throw with `[Throws]`. `ArgumentNullException.ThrowIfNull(a)` of a
non-nullable array or class reference is nothing: such a reference is non-null (R10.2
for a class; an array is translated as owned and so live), so the guard never fires.

### R23.3 Exception arguments

A BCL exception's constructor arguments (R21.7) may be constants or reads of a local or
parameter, as in `new ArgumentOutOfRangeException(nameof(i), i, SR.Message)`: they have no
effect, and the exception is modelled by its type alone, so they are not evaluated.

### R23.4 `Array.Resize(ref a, n)`

is `a = resize a n`: a fresh array of length `n` whose first `min(len a, n)` cells are
`a`'s and whose rest are `default(T)` (`resized`, with `resized_length` and
`resized_prefix` patterned). The old array is kept rather than consumed, because a field
replaced in an open object drops what it held (R22.12).

### R23.5 `Array.LastIndexOf(a, x, start)`

with an effect-free `start` is R22.25's search over `[0, start]` from the top.
`last_index_of_found_iff` (patterned) states that a search from either end of a range
finds something exactly when the other does, so `Contains` may be specified by
`Pal.IndexOf` and implemented by `LastIndexOf`.

### R23.6 Array distinctness in `Debug.Assert`

`Debug.Assert(a != b)` is erased under R22.19. The library's explicit `distinct a b` proves
`a =!= b` from both being owned, when one of them has a cell (the gathered permission
would exceed 1). Two empty arrays may be the same object — `Array.Empty<T>()` is shared —
so the step needs `length a > 0 \/ length b > 0` of its context.

### R23.7 `[DoesNotReturn]` on the open receiver

A call to a `[DoesNotReturn]` instance method on the receiver (R22.11) closes the receiver
once, as at a `throw`, and calls it closed; R22.15's bracket around a self-call is not
added, since nothing follows the call to reopen it for.

### R23.8 Split guards

`if (a || b) throw …;` with no `else` is `if (a) throw …; else if (b) throw …;`. Lowered as
one `if`, a `b` that needs statements (an array's length, a field read) leaves the
condition a bound `bool` Pulse knows nothing about, and what follows cannot use the
guard's failure; split, each disjunct's failure is a path condition of its own. The throw
is duplicated, which is harmless: it is reached on exactly the paths it was.

### R23.9 Writes in an element target

The index of an element assignment is evaluated too, so `a[--j] = x` assigns `j` for
R5.8b: a loop containing it quantifies `j` in its invariant.

### R23.10 `Pal.Ring(s, h, n)`

⟶ `CS.ring ⟦s⟧ ⟦h⟧ ⟦n⟧`: the `n` live elements of a circular buffer whose head is at
`h`, wrapping once — `s[h + k]` when `h + k < len s`, else `s[h + k - len s]` — for
`0 <= h <= len s` and `0 <= n <= len s` (else empty). Stated by that index equation
(`ring_index`, patterned) rather than with a modulus, so that a head or tail moving by
one is index arithmetic. `ring_length` is patterned on the ring itself, so that two
states whose rings are equal (R22.15's model equality across a self-call) have equal
counts. `ring_index_of` reads a search of a ring as one search of the store, or two when
the live range wraps: `Queue<T>.Contains`' two `Array.IndexOf` calls.

### R23.11 A field passed by `ref`

A call `M(ref _f)` on the receiver, where `_f` is a scalar field of the class and `M`'s
body names neither `_f` nor any method, is `{ var t = _f; M(ref t); _f = t; }` (R6.10 needs
a `ref` argument to be a cell). The copy is exact: `M` cannot observe `_f` while it runs.

### R23.12 `Math.Min` and `Math.Max`

at `int`, of effect-free arguments, are the conditional `a <= b ? a : b` (`a >= b ? a : b`).

### R23.13 `[]`

An empty collection expression at an array type is `new T[0]` (and trusted as R23.1 is:
the compiler may share `Array.Empty<T>()`).

### R23.14 Two-state sequence equality

R22.23's `Seq.equal` is used also when an abstraction of one state is compared with one
of the other (`Items == Old(Items)`), and when a conditional's arm is built or old: what
the method did to the representation lies between the two sides, so the solver must
compare them pointwise; the patterned `lemma_eq_elim` restores `==` at a caller. An
array's contents are a name in either state, so a frame `Contents(a) == Old(Contents(a))`
stays `==` (as a loop invariant, `Seq.equal` there costs the solver an extensionality
quantifier per iteration for nothing).

### Queue<T>

`Queue<T>`'s model is `Items = Ring(Contents(_array), _head, _size)` with the store and
head alongside, so that a model equality across a read-only self-call (`MoveNext`)
determines the raw state. The invariant states `_tail` as `_head + _size` wrapped once.
`CopyTo`'s second destination index `arrayIndex + _array.Length - _head` can overflow in
its first addition and is correct only because unchecked arithmetic wraps back; the
method is verified as `[Wrapping]` for that reason.

### LinkedList<T>: not verified

`LinkedList<T>` (System.Collections) is a *circular* doubly linked list of
`LinkedListNode<T>` objects, each of which also points back at its list. Marking both
classes `[Plain]` (§12) and translating `LinkedList.cs` in place stops at four distinct
obstacles, each confirmed by a probe:

1. **An untranslatable field.** `LinkedList<T>._siInfo : SerializationInfo?` (binary
   serialization state) has no translation, so `LinkedList<T>`'s record cannot be emitted
   at all (PALCS0500). Needed: an *opaque field* — a field no translated member reads,
   emitted as an abstract placeholder type.
2. **Mutually referencing classes.** `LinkedList<T>.head : LinkedListNode<T>?` and
   `LinkedListNode<T>.list : LinkedList<T>?` make `Class_LinkedList` and
   `Class_LinkedListNode` depend on each other, and F\* refuses the module cycle (Error
   308). Needed: the classes of a reference cycle emitted as one module of mutually
   recursive types (`type … and …`), with per-class modules re-exporting it by `include`.
3. **Constructors of a `[Plain]` class.** `AddFirst(T)`/`AddLast(T)` allocate with
   `new LinkedListNode<T>(this, value)`; R12.4 accepts only object-initializer syntax.
   Needed: a `[Plain]` constructor given an explicit contract (`[Ensures]` an `SlProp`
   cell), translated like any method rather than read for field assignments.
4. **Aliasing inside one statement.** `InternalInsertNodeBefore` (behind every `Add*`)
   executes `node.prev!.next = newNode`, which reads `node` and writes `node.prev` in a
   single statement. On a one-element list `node.prev == node`; otherwise they are
   distinct boxes. A per-node `pts_to` encoding needs *one* resource in the first case and
   *two* in the second, but the statement is one straight-line Pulse step with no branch
   to split on, and Pulse matches a box by unification, not by an SMT equality, so no
   ghost step placed between C# statements can serve both. Needed: either a *region*
   encoding of `[Plain]` objects (all nodes owned by one ghost map, a field access proving
   membership, so aliasing is a pure fact), or an emitter rule that, at a statement whose
   two box accesses may alias, case-splits on the reference equality and emits the
   statement in each branch.

Removal (`RemoveFirst`/`RemoveLast` via `InternalRemoveNode`) does not meet obstacle 4 —
the code itself branches on `node.next == node` before touching a second node, and in
the two-element case the two writes are separate statements between which a ghost
lemma can re-open the segment — so with 1 and 2 removed it is within the §12 method:
a circular-segment predicate over `head` (closed through `head.prev`) and a `[Plain]`
receiver whose record the user's predicate owns. `Count` and `First` are field reads of
that record; `Last` (`head?.prev`) reads the head node and needs only the predicate's
"open first node" lemma.

### Trusted

Beyond §22's: R23.1's (and R23.13's) reading of the shared empty array as fresh, and R23.2's trust that a
non-nullable reference is not null.

## 24. Hashing

`HashSet<T>` and `Dictionary<TKey,TValue>` keep their elements in an `Entry[]` of
`(hashCode, next, value)` structs threaded into chains from an `int[]` of 1-based bucket
heads, with removed entries linked into a free list through the same `next` field. Both
arrays are `null` until the first insertion, and the comparer is an
`IEqualityComparer<T>?` that is `null` for the default. The harnesses are `pal/HashSet`
and `pal/Dictionary` in the runtime checkout; `test/collections_hashing` pins each rule
below on a smaller table.

The translator sees the runtime's sources with only `PAL` defined, so `TARGET_64BIT` is
off: `GetBucket` is `buckets[(uint)hashCode % (uint)buckets.Length]`, and the
`_fastModMultiplier` field and `HashHelpers.FastMod` are not part of the verified code.
The two compute the same bucket (that is `FastMod`'s own contract); the 64-bit path is
not verified.

### R24.1 `unsafe` members compile

Production sources contain some `unsafe` code. The harness passes `PAL_CS_FLAGS = --unsafe`
(R25.11) so that it compiles; such a member is refused only if something asks for it to be
translated.

### R24.2 A comparer is a value field

A field whose type is a `[SpecType]` or a bound library type (R20.11, R21.5) — an
`IEqualityComparer<T>?` — is held in the class's record like a field at a type parameter
(R15.5): the type is opaque, so nothing but the record can own it.

### R24.3 An invariant sees private nested types

Like `[Model]` (R4.10b), an `[Invariant]` describes the representation, so it may mention a
field whose type is a private nested type (`HashSet<T>.Entry[]`). Its shim is bound with
accessibility checks off; every other error, and every inaccessibility outside an
invariant, is still reported.

### R24.4 Effectively sealed

Under `[TranslateAnnotatedOnly]`, a class whose only virtual members are unannotated
(`HashSet<T>` implements `ISerializable` through a virtual `GetObjectData`) is treated as
sealed (R22.5): an unannotated virtual has no module, so no translated body calls it, and
an override changes nothing that was verified.

### R24.5 The program's own collection

R20.4 reads a BCL `HashSet<T>`/`Dictionary<K,V>` as an opaque model. A type whose source
is part of the compilation is the program's own and is translated as written.

### R24.6 Nested structs of generic classes

A struct nested in a generic type (`HashSet<T>.Entry`) is generic in the outer type
parameters, which come before its own. Its module name is qualified by the outer type
(`Struct_HashSet_Entry`), because `Dictionary<K,V>` has an `Entry` too.

### R24.7 Nullable array fields

An array field declared `T[]?` is owned through `Pulse.Lib.CSharp.NullableArray.pts_to`
(verified): a `null` reference owns nothing and holds the empty sequence, and a non-null
one owns its cells exactly as `A.pts_to` does. The parts that differ from R22.12:

- A constructor that does not assign the field leaves it `null`. A null written by the
  constructor or by a method is a fresh name from `NA.alloc_null`, and a non-null array
  moves in by `NA.intro`, which also records that the reference is not null.
- Reading, writing or bulk-operating on the field opens it with `NA.elim` under a
  non-null fact and closes it again with `NA.intro`. In both code and specs, `a == null`
  is `A.is_null a`; nullness is a property of the reference, which a spec binds next to
  the contents.
- An invariant over such a field can say how its nullness relates to the other fields
  (`(_buckets == null) == (_entries == null)`, `_entries != null || _count == 0`). In a
  spec, `_entries.Length` is the length of the contents, which is 0 while the field is
  null.

### R24.8 `ref` locals

`ref Entry entry = ref entries[i];` names an array element. Its index is evaluated once, into
a fresh local, and every use of `entry` reads or writes the array element at that local:
in code and in specifications alike. This is C#'s meaning while the array the alias points
into stays the same. So the rule applies only when:

- the local is never rebound (`entry = ref …`);
- the array is named by a local that is not reassigned (R24.19 makes a field's local
  qualify), or by a field;
- for a field, or for an array produced by a call, nothing in the local's scope assigns a
  field the alias depends on, or calls a non-`ref`, non-`[Lemma]` instance method of the
  class. The fields an alias depends on are the array's own field, or, for an inlined
  `ref`-returning call (R24.9), every field its body mentions. So `Remove` may assign
  `_freeList` while `bucket` aliases `_buckets[…]`.

Any other `ref` local is refused (PALCS0001).

### R24.9 Inlining `ref`-returning helpers

A call to a `ref`-returning method whose body is a sequence of single-variable local
declarations followed by `return ref e;` is replaced by `e`, with the parameters and locals
substituted. The call must be on `this` or have no receiver, and its arguments must be
names or constants, so substituting them changes no evaluation order. With R24.8 this is
what turns `ref int bucket = ref GetBucketRef(hashCode);` into an element of `_buckets`.

### R24.10 `Array.Clear(a)`

`Array.Clear(a)` clears the whole array: it is `Array.Clear(a, 0, a.Length)` (R22.25).

### R24.11 The default of a code struct

A struct that is not `[Spec]`, has no `[Refine]`, and whose fields are all machine
integers, `bool`s or type parameters has C#'s `default(S)`. This is the `has_default`
instance that sets every field to its default, and it requires `has_default` for each
type parameter. So `new Entry[n]` and `Array.Clear(entries, …)` need the caller's
defaults for the type parameters that `Entry` mentions (R22.22).

### R24.12 Ghost locals

A local of type `Ghost<T>` that is initialised and never assigned is a ghost `let`. It names
a specification value fixed at its declaration (`Ghost<Seq<int>> before = Pal.Contents(a);`)
that later ghost statements can mention, and it has no run-time existence. A snapshot of
a machine integer (`Ghost<int> length0 = entries.Length;`) is its mathematical value, an
F* `int`, as every machine integer in a specification is. A loop that writes a field may
not name that field in its measure (F3), so a snapshot is how such a loop is measured:
`Pal.Invariant(entries.Length == length0.Value); Pal.Decreases(length0.Value - n);`.

### R24.13 What is trusted

`Pulse.Lib.CSharp.Equality` (an interface, every `val` a modeling axiom) is the trusted base
for hashing:

- A comparer is an opaque handle. Its `Equals` and `GetHashCode` are functions:
  deterministic, terminating, and without effects.
- The one law the tables need is `equals_hash`: equal values hash alike. This is the
  `IEqualityComparer<T>` contract.
- `EqualityComparer<T>.Default.Equals` is R22.25's `default_equals`. `x.GetHashCode()` on a
  value of a type parameter is the default comparer's hash.
- `typeof(T)` is an opaque type handle, and `IsValueType` is a function of it.

The R21.5 bindings that attach these to the BCL's members live in the harness
(`pal/HashCommon/Bindings.cs`). `Pulse.Lib.CSharp.NullableArray` and
`Pulse.Lib.CSharp.HashChain` are proved, and assume nothing.

`Pulse.Lib.CSharp.Null.is_null` (`x == null` at a type parameter) is a trusted `val`
shared with R25.4. The harness's `ThrowHelper` (`pal/common/ThrowHelper.cs`) is a
stand-in whose members only throw. Choosing the 32-bit bucket computation (above) is
an assumption about which path is verified, not a fact the proof establishes.

### R24.14 `return` inside a loop

A `return e` inside a `while`/`for` body sets a "returned" flag and a result cell, and
then leaves the loop. The loop condition is conjoined with `!returned`, and the code after
the loop runs only when the flag is clear; when it is set, the method returns the cell.
So a loop's invariant has to say what a return inside it established:

- `Pal.Returned()` is the flag. Using it outside a loop is an error (PALCS0645).
- `Pal.Result<T>()` inside a loop invariant is the result cell.

The usual shape is `Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.Result<int>() >= 0 && …))`.
If a loop has no `break` of its own, the loop breaks on the flag itself (R5.10), so after
the loop "not returned" means "the condition failed". If the loop does have its own
`break`, that `break` keeps its separate cell.

*Integration note.* The rewrite itself is R26.2's (the frontend's, which also handles any
result type with a default); R24.14 names the same cells, so `Pal.Result<T>()` inside a
loop and R26.2's `Pal.ReturnValue<T>()` are synonyms. What R24.14 adds on top is a
normalization: when the loop sits inside an `if` that something follows, what follows is
copied into both arms of that `if`, so that R26.2's `if (returned) return …` and the
statements after it are in one block, where R5.5b moves the rest under the guard.

### R24.15 `typeof(T)`

When `System.Type` has an R21.5 binding (the hashing harness binds it), `typeof(T)` is
`Equality.type_of T`, an opaque handle. It is never null, whatever the nullable context says.
`typeof(T).IsValueType` is then the bound function applied to that handle.

### R24.16 Unsigned indices and counters

An array index of type `uint`, `long`, `ulong`, `nint` or `nuint` is converted to `int`
(`(uint)h % (uint)len` is an index below `len`, so the conversion is exact). The proof
obligation is that the value fits, and F* warns that `uint32_to_int32` is deprecated
(PALCS0601). The `1` in `x++`/`x--` has `x`'s type, so a `uint` counter adds `1ul`.

### R24.17 Specification functions defined in F*

A `[Spec]` method may carry `[PulseBody("…")]`. Its F* definition is the given text, with
`$(p)` naming a parameter (R4.9), and its C# body (conventionally `=> throw …`) is not
looked at. A `bool` result is a `prop`, and a machine-integer result is an `int`. This
is how a theory that is proved in F* (`Pulse.Lib.CSharp.HashChain`: chain
well-formedness, membership, the chain-search invariant) is named from C#.

Only a `[Spec]` or `[Lemma]` method's body is skipped this way; a code method with
`[PulseBody]` is still lowered, so a code method with two bodies is still refused
(PALCS0503).

Such a function is not an observation (R9.21). A class module opens the spec-function
modules named by its invariants, model, refinements and observations, and so does every
method that takes the class, because the method unfolds the invariant.

The contracts of a `private` member may name the class's private members and nested types,
the same way an invariant may (R24.3). The shim for the contract is bound with accessibility
checks off. Inside a shim the helpers are reached as `C<T>.Name(…)`.

### R24.18 Specification values in a `[Spec]` struct

A `[Spec]` struct (R3.9a) may hold a field of a `[SpecType]` or bound type, and `T?` of
one. An example is the comparer, `IEqualityComparer<T>?`, in `HashSetModel<T>`. These are
pure F* values, so they own nothing. A public contract then reads the comparer through
an observation of the model (`@this.SpecComparer`) rather than through the private field.

### R24.19 A local copy of an array field

`T[]? a = _field;`, at the head of a method, is another name for the field. The rule
applies when the local is never assigned or passed by `ref`/`out` (writing an element is
fine: it writes the field's array), and when nothing in its scope assigns that field or
calls another instance method of the class. Every use of `a`, in code and in
specifications, is then the field. Without the rule the local is a cell holding a
reference, and nothing would tell the verifier that this reference is the one the class
invariant describes.

### R24.20 Static members of generic library types

A static member of a generic type bound by R21.5 (`EqualityComparer<T>.Default`) takes the
type's arguments as its leading explicit arguments (`default_comparer T`). If the library
declares the member non-nullable, it is not an `option` even in a nullable-oblivious
specification.

### R24.21 A field of an array element

`a[i].f = v`, for `a` an array of a code struct, reads the element, and writes it back
with the field replaced: `write a i { cur with f = v }`. It counts as a write of the
array, not of the struct, so it is what a loop's frame and R5.12's representation see.
Through a `ref` local (R24.8), `entry.Next = …` is the same write.

### R24.22 Immutable locals in loop invariants

A local that is bound once (R5.2a), and a ghost local (R24.12), may be named by a loop's
invariants and measure. It is the same value at every iteration, so it is bound in the
invariant's scope as itself, as it already is in the body. `Remove`'s invariant can then
say `_comparer == comparer` of the local it hashes with.

### R24.23 `x!` and `x is null` at the translation's types

`x!` is transparent (R10.5) except where `x` is an `option` (a nullable reference of a
bound type, such as `IEqualityComparer<T>?`): there C# types `x!` at the non-nullable
type, and its translation is the value, `Some?.v x`. The refinement of `Some?.v` is the
proof obligation that `x` is not null. This is how `comparer!.GetHashCode(item)` reads.

`x is null` and `x is not null`, for `x` of a type with an opaque null (R25.4: a type
parameter that may be instantiated at a reference type), test `is_null x`. Before this
rule they were the constant `false`, which is unsound for a `T` instantiated at a
reference type; `HashSet<T>` hashes `item is not null ? comparer.GetHashCode(item) : 0`.

### R24.24 A loop arm that writes a field

A loop body is in tail position (R5.8d). When one of its statements, other than the last,
is an `if` with an arm that assigns a field of the receiver, the statements that follow
are moved into both arms. Statements after an escape (R5.10, R24.14) are still guarded by
the escape test, again in tail position. Each arm is then checked against the loop
invariant rather than joined first. Pulse joins differing record values as a `match` on
the condition. No array field can then be found through a projection of that `match`.
`Remove`'s found arm writes `_freeList` and `_freeCount` and returns, and needs this rule.

### R24.25 Nullable arrays are matched by their reference

`Pulse.Lib.CSharp.NullableArray.pts_to`, the resource for an array that may be null, marks
the array as its matching key (`[@@@mkey]`), as `Pulse.Lib.Array.pts_to` does. Pulse then
finds the resource by its reference and proves the contents and permission equal by SMT,
rather than by unification. It matters after an `if` whose arms write different arrays
(`bucket = …` in one arm, `entries[last].Next = …` in the other). Pulse's join states each
array's contents as a `match` on the condition, and unification cannot equate that with
either arm's contents.

## 25. Sorted collections

dotnet/runtime's `SortedList<TKey,TValue>` is two parallel arrays kept in key order by an
`IComparer<TKey>`, searched with `Array.BinarySearch`. Its model is a strictly sorted
`Seq<TKey>` of keys with a `Seq<TValue>` of values position for position, and the comparer
itself (harness `pal/SortedList` in the runtime checkout). `test/collections_sorted` pins
each rule below on a smaller sorted key set. §25.2 records why `SortedSet<T>` and
`SortedDictionary<TKey,TValue>` are not yet within reach.

The library is `pulse/Pulse.Lib.CSharp.Sorted.fst`. Over R22.30's `Order.comparer`, it defines:
`sorted`, `strictly_sorted`, `lower_bound` (how many elements are less than `x`) and
`key_index` (`lower_bound` if the element there compares equal, else `-1`); and the
specification `range_search` of the BCL's `InternalBinarySearch`. It also has a Pulse
`range_search_array` **proved** to compute `range_search`. Its lemmas, with SMT patterns,
say what the result means on a sorted range:
* a hit is `index + lower_bound` of the slice, and compares equal;
* a miss is `~(index + lower_bound)`.

### R25.1 Comparers

`IComparer<T>` and `Comparer<T>` are the spec type `Pulse.Lib.CSharp.Order.comparer T`: a
ghost value, which a `[Spec]` struct and a class field may hold (an object's comparer is a
pure conjunct of its invariant, not a resource). `Comparer<T>.Default` is
`Order.default_comparer`. `c.Compare(x, y)` in code is `Sorted.compare_i32 c x y`, an
`int` whose sign is `Order.compare`'s. A constructor that assigns a comparer field on
every path is given `default_comparer` as the stand-in its representation starts from.

### R25.2 `notnull`

A `where T : notnull` constraint is accepted and has no translation: it is a nullable-flow
annotation, and the model never relies on it.

### R25.3 Fields that do not translate

Under `[TranslateAnnotatedOnly]`, a field whose type has no translation is left out of the
representation, as an unannotated member is left out of the class. Examples are a cached
view object (`SortedList`'s `keyList`/`valueList`) or a serialization temporary. Translated
code that reads or writes such a field finds no field and is refused.

### R25.4 Null tests

`x == null` and `x != null` on a type parameter or a comparer, which have no `Box` to test,
are `Sorted.is_null x` (trusted, below). `c ?? d` on a comparer is
`if is_null c then d else c`. `Pal.IsNull(x)` names the test in a contract.

### R25.5 `Array.BinarySearch`

`Array.BinarySearch<T>(a, index, length, value, comparer)` in code is the proved
`range_search_array`. Its comparer is wrapped in `or_default` (`null` means
`Comparer<T>.Default`, as in the BCL) unless the comparer's nullable flow state is
not-null. Its contract reflects the BCL's: the range must be within the array, and the
result is `range_search` of the contents. `~r` of a negative result is the insertion point
(`lognot_negative`, patterned on the idiom). A method whose only use of an array is a
binary search does not mutate it (as `IndexOf`, R22.25).

### R25.6 Specification intrinsics

`Pal.Compare(c, x, y)`, `Pal.Sorted(c, s)`, `Pal.StrictlySorted(c, s)`,
`Pal.LowerBound(c, s, x)`, `Pal.KeyIndex(c, s, x)` and `Pal.BinarySearch(c, s, i, n, x)`
are the library functions of the same names (`doc/surface_syntax.md` §1.3). `KeyIndex` is
the natural model of a sorted map's `IndexOfKey`, and `LowerBound` of where an insertion
goes.

### R25.7 Argument guards

`ArgumentNullException.ThrowIfNull(x)` on a type parameter or a comparer is
`if is_null x then throw`, and `ArgumentOutOfRangeException.ThrowIfNegative(n)` on an
`int` is `if n < 0 then throw`. Both are throw points like any `throw` (§19).

### R25.8 `Array.Empty<T>()`

is a fresh array of length `0`. The BCL caches it, but a zero-length array has no contents
for sharing to be observable through. (Implemented by R23.1, in code position; the two rules were written in parallel.)

### R25.9 Exception messages

The arguments of a library exception's constructor that only build its message are
evaluated for no effect: `SR.*`, `SR.Format(…)`, `nameof`, `ToString()`, a parameter or a
local. Messages are not modelled (R21.7), so the exception is the throw point alone.

### R25.10 A call that moves a closed receiver ends the join

R22.12 extended: when an arm of a statement-position `if` calls a method that moves a
receiver's model, the `if` does not join, and the statements after it are emitted in each
arm. The receiver's post-state is an existential, which Pulse's join generalises afresh.
Joining would lose what the call ensured, and also the other arm's fact that the receiver
is unchanged. `SortedList.Remove` (`if (i >= 0) RemoveAt(i); return i >= 0;`) is the case.

### R25.11 Compiling a runtime source as it is built

`palcs --preview` compiles with `LangVersion=preview`, and `palcs --unsafe` allows `unsafe`
blocks; `verify.mk` passes `$(PAL_CS_FLAGS)` through. dotnet/runtime builds its libraries
that way (`SortedSet.cs` uses `?.=` and `stackalloc`). The translator still refuses unsafe
code in any member it translates.

### R25.12 Partial classes

A `partial` class is collected once. It is collected at the declaration that holds its
`[Model]` member, or else at its first declaration, rather than at every declaration.

### 25.1 Trusted assumptions

* `Sorted.is_null` is an uninterpreted test (R25.4). Nothing is assumed about it except that
  it is a function.
* A comparer is a pure, deterministic total preorder (R22.30, shared). `Compare` has no
  effect and does not throw.
* `Array.BinarySearch` is the BCL's `InternalBinarySearch`: lower half on a negative
  comparison, `~lo` on a miss. The Pulse function is proved against that specification.
  Its agreement with the BCL is trusted.
* `ThrowIfNull`/`ThrowIfNegative` throw exactly on the stated condition (R25.7).
* Building an exception message has no effect and does not throw (R25.9).

### 25.2 What blocks `SortedSet<T>` and `SortedDictionary<TKey,TValue>`

*Update:* §27 removes obstacles 1 to 6 for `SortedSet<T>`'s read-only members, by other means than
the ones proposed below:

* exact-type verification (R27.1);
* a `[Region]` node class, whose auto-properties are its fields (R27.3);
* the owner holding the whole region (R27.4);
* loops over `Pal.Tree` (R27.7);
* R26.2's `return` inside a loop;
* a returned pointer that the caller only tests against `null`.

Obstacles 7 and 8 still stand. §27.2 lists what is verified. `SortedDictionary`'s core
members are verified too (R27.57–R27.59).

`SortedDictionary` is a wrapper over `SortedSet<KeyValuePair<TKey,TValue>>` (`TreeSet`), so
both wait on `SortedSet`. The harness `pal/SortedSet` in the runtime checkout gets
through the C# compiler with R25.11 and R25.12, and is then refused. These are the
obstacles, in the order a verification would meet them, each with what pal-csharp needs:

1. **A generic class hierarchy.** The nested `TreeSubSet : SortedSet<T>` (the view
   `GetViewBetween` returns) overrides `FindNode`, `MinInternal`, `MaxInternal`,
   `IsWithinRange` and `VersionCheck`, and `Contains`/`Min`/`Max` dispatch through them.
   R15.1 refuses a generic base (PALCS0581). Treating `SortedSet<T>` as closed (R22.5) would
   be unsound, because a `TreeSubSet` receiver runs the overrides. *Needs:* §9's vtables at
   a type parameter, and contracts on `internal virtual` members that the overrides are
   checked against.
2. **Auto-properties as a node's fields.** `Node`'s `Item`, `Left`, `Right` and `Color` are
   `{ get; set; }`. A read of `current.Left` is taken as a member call (PALCS0523), not as
   the field R10.5's `[Model]` would be written over. *Needs:* an auto-property of a
   recursive class read and written as its backing field.
3. **A recursive structure owned through another object's field.** The tree hangs off
   `SortedSet.root`. §10 opens a node's window only at an `if` whose whole condition is the
   null test of a local or a parameter (R10.7). `root == null` on a field, and
   `FindNode(item) != null` as a value, are refused (PALCS0569, PALCS0593, `IrNull`). A
   `[Spec]` struct cannot hold a `SpecTree` either (PALCS0511), so the model cannot pair the
   tree with its comparer. *Needs:* a class field of recursive type owned through
   `__inv_opt`, with the window opened at a field null test, and `SpecTree` admitted as a
   ghost struct field.
4. **Iterative descent.** `FindNode`, `MinInternal`, `MaxInternal` and every mutator walk
   the tree with a `while` loop over `current`. §10.7: a loop over a derived recursive
   invariant cannot name the part already passed. §16 (`test/tree_cursor`) does it for a
   `[Plain]` node with a hand-written one-hole-context predicate and a ghost lemma call per
   step. That is admissible in place (ghost statements only), but `[Plain]` excludes a
   `[Model]` owner. *Needs:* a derived path predicate (zipper) for a §10 class, so that
   a descent loop's invariant can be `Spine(root, cur) ** Holds(cur, sub)`.
5. **`return` inside a loop.** `FindNode` returns the matching node from inside its loop.
   R5.5b refuses that rather than invent a flag.
6. **Returning an interior pointer.** `FindNode` returns a `Node` that the tree still owns.
   `Contains` only tests it against `null`, but its contract must say what the caller
   holds. *Needs:* a borrowed (magic-wand) return, or a ghost-only nullness result.
7. **The order lives outside the nodes.** The BST invariant (`Item`s ascend under the set's
   comparer) has to be a `[Refine]` on the set's model, over the tree, using a
   `tree_sorted c t` analogue of `strictly_sorted`. A node's derived invariant cannot
   mention the comparer. This is a small library addition once 3 holds.
8. **Insertion and deletion.** These are top-down 2-3-4 algorithms with four simultaneous
   interior pointers (`current`, `parent`, `grandParent`, `greatGrandParent`) and rotations
   that re-link them. Beyond the red-black colour invariants, they need simultaneous
   ownership of several overlapping path segments, which is beyond §16's single cursor.

`comparer = default!` (a field initialiser of `default` at a comparer type) is also refused.
That is minor: it could be R25.4's null comparer.

## 26. The rest of `List<T>`, and `PriorityQueue<TElement,TPriority>`

The rest of dotnet/runtime's `List<T>` comes after §22's core:
* the delegate-taking members (`Find*`, `Exists`, `TrueForAll`, `RemoveAll`, `ForEach`);
* `Sort` and `BinarySearch` with a comparer;
* the capacity heuristics.

`PriorityQueue<TElement,TPriority>` (System.Collections) is an array-backed 4-ary min-heap
of `(element, priority)` pairs ordered by an `IComparer<TPriority>`. Its model is the
`Seq<(TElement, TPriority)>` of live nodes, the comparer, and the capacity. The heap
property is a contract (`Pal.IsHeap`) on the members that need it rather than a class
invariant, so that `Clear`, `EnsureCapacity` and `TrimExcess` need not re-establish it.

The harnesses are `pal/List` and `pal/PriorityQueue` in the runtime checkout.
`test/collections_listrest` pins each rule on smaller code. The libraries are:
* `pulse/Pulse.Lib.CSharp.Delegate.fsti`: the delegate model, trusted;
* `Find.fst`: the search, filter and map functions, proved;
* `Sort.fst`: a Pulse insertion sort proved to meet `sorted_range`;
* `Heap.fst`: the 4-ary heap theory and the sift-loop lemmas, proved;
* `Scale.fsti`: trusted;
* `Comparer.fsti`: the `null` comparer, trusted.

### R26.1 Callable delegates

`Predicate<T>`, `Action<T>`, `Converter<TIn,TOut>` and `Comparison<T>` are
`Delegate.fn1`/`fn2`. A call `d(x)` or `d.Invoke(x)` is `apply1 d x`, in code and in a
contract alike, so `[Ensures("Result == Pal.FindIndex(@this.Items, match)")]` means what
the loop computes. `d == null` is `is_null1 d`. Verified code calls a delegate but never
creates one, so a method group converted to such a type is refused (PALCS0685). A delegate
is a pure function (R26.12), so `Action<T>` has no observable effect and `ForEach`'s
contract is only that the list is unchanged.

### R26.2 `return` inside a loop

`return e;` inside a loop is `{ __pal_result = e; __pal_returned = true; break; }`. Each
enclosing loop that a `return` leaves breaks on the flag, and after the outermost one the
method returns the value if the flag is set. The value cell starts at the type's `default`,
so a return type with no `default` in the translation is refused (PALCS0686). In an
invariant, `Pal.Returned()` and `Pal.ReturnValue<T>()` name the two cells.

### R26.3 Search and filter specifications

`Pal.FindIndex`, `FindLastIndex`, `TrueForAll`, `FindAll`, `RemoveAll` and `ConvertAll`
are `Find.fst`'s functions over a delegate. The windowed forms take the BCL's
`(startIndex, count)` and `(startIndex, count)`-backwards conventions.

### R26.4 A read's binder is not rebound

An immutable local whose initialiser is already a read's binder (`tN`) is that binder,
not a second `let`. A second `let` is opaque to Pulse's prover, and an `if` that mentions
it could not be joined. Parenthesisation of atoms in the emitter was also corrected.

### R26.5 A loop body's `if` that calls a local object's method

In a loop body, an `if` one of whose arms calls a method on a local object is split: the
statements after it move into both arms (as R22.12 does in a method's tail). Otherwise
Pulse's join keeps the other arm's facts about the object only under that arm's condition.
`FindAll` adding to its result list is the case.

### R26.6 Scaled integers

`(int)(n * c)` and `(int)((double)n * c)`, for a literal `0 <= c <= 1`, is
`Scale.scale_unit n`: between `0` and `n`, on the side of `n`'s sign. The translation has
no floating point. This is the BCL's capacity threshold (`TrimExcess`'s
`(int)(_items.Length * 0.9)`).

### R26.7 Sorting with a comparer

`Array.Sort<T>(a, index, count, comparer)` is `Sort.sort`, a Pulse insertion sort
**proved** to establish `Pal.SortedRange(old, new, index, count, comparer)`:
* the range ascends under `comparer ?? Comparer<T>.Default`;
* the range is a permutation of what it held;
* everything outside the range is unchanged.

The BCL's introsort is not translated. Only its specification is assumed to be the one the
proved sort meets, and a caller cannot distinguish the two except by stability, which
neither promises. A `null` comparer is `Comparer.null_comparer`, the comparer that
`Sorted.is_null` holds of. `Pal.Permutation(s, t)` is the bijection-based permutation.
`List.BinarySearch` uses §25's proved `Array.BinarySearch`.

### R26.8 Value tuples

`(T1, T2)` is F*'s `tuple2`:
* `(a, b)` is `Mktuple2`;
* `.Item1`/`.Item2`, or a named component, is a projection;
* `default` is the pair of defaults;
* `(a, b) = e` reads `e` once.

A tuple-typed local's `let mut` carries its type, because Pulse needs the pair's universe
to be 0. This is `PriorityQueue`'s node type.

### R26.9 Retired

It was `Array.Resize`, which is now R23.4.

### R26.10 Heaps, `Pal.Broke()`, and array aliases in loops

* **Heap specifications.** `Pal.IsHeap(s, c)` says that every node's priority is at least
  its parent's, the parent of `i` being `(i - 1) / 4`. `Pal.HeapMin(s, x, c)` says that no
  node of `s` is below `x`. `HeapUp`/`HeapDown` are the sift loops' invariants: a hole `h`,
  the node `x` on its way to it, every edge not touching the hole in order, and `s` with
  `x` in the hole a permutation of the original. `HeapUpStop`, `HeapDownStop` and
  `HeapMinChild` are the exit conditions and the inner min-child scan. `Heap.fst` proves a
  lemma per step (init, step, stop, finish, remove-root, replace-root), which the C# calls
  as `[Lemma]`s.
* **`Pal.Broke()`.** In an invariant, `Pal.Broke()` is the loop's break flag. The loop
  exits as soon as the flag is raised, so `Pal.Implies(Pal.Broke(), P)` records what held
  at the `break`. A `break` skips a `for`'s step.
* **Array aliases in loops.** An array-typed local that the loop does not rebind keeps its
  equality with the array it aliases across the loop (`var nodes = _nodes;`). An element
  write through such a local, or passing it to a call, counts as a write to every array
  field of the receiver, so those fields' contents are not carried across the loop as
  unchanged.
  * A `decreases` measure reads such a local's length as `arr_length`.

### R26.11 Assignment expressions and guards that write

`(x = e)` in expression position, for a local `x`, is the write followed by a snapshot of
`x`. A `while` guard that begins with such an expression, or with `++x`/`--x`, compared
against an operand that reads none of the written locals, becomes a `for` whose init and
step are the write and whose test is the comparison:
* the guard's effect runs before each test;
* a `continue` still runs it;
* the invariant describes the state just after it.

Examples are `while ((i = GetFirstChildIndex(nodeIndex)) < size)` and `while (++i < bound)`.

### R26.12 Delegate purity (trusted)

R26.1's model is an axiom. See §26.1.

### R26.13 `is null` on a comparer

The pattern `c is null`, on a type whose null test is R25.4's opaque `is_null`, is
`Sorted.is_null c`, as `c == null` is. Before this rule, it lowered to `false`.

### 26.1 Trusted assumptions

* **Delegates (R26.12).** A delegate is a pure, total, deterministic function. Invoking it
  does not throw and touches no state that verified code owns, in particular not the list
  that calls it. `fn1 a r = bool & (a -> r)` is a model, so the axioms are consistent. A
  BCL caller may pass an impure delegate. What the specification then promises is only
  what holds for a pure one, and `List`'s `_version` check, which catches a delegate that
  mutates the list, is not modelled.
* **Scaling (R26.6).** `scale_unit`'s range is exact for every `int` and every literal in
  `[0, 1]`, but it is not proved.
* **Comparers.** They are R22.30's total preorder. The existence of a `null` comparer is
  `Comparer.null_comparer`.
* **`Array.Sort` (R26.7).** Its result is assumed to meet the specification that the proved
  insertion sort meets.

### 26.2 Specification findings

* **`PriorityQueue` child-index overflow.** `GetFirstChildIndex` computes
  `(index << 2) + 1`, which wraps once `index >= 2^29`.
  * `MoveDown` is entered with `nodeIndex = 0`, and it descends while a child exists.
  * In a queue of more than `2^29 + 1` nodes, a node at `index >= 2^29` would compute a
    negative first child. The guard `i < size` would then hold and the read would throw
    `IndexOutOfRangeException`.
  * `Array.MaxLength` (`0x7FFFFFC7`) allows that many 16-byte nodes, given enough memory.
  * Contracts therefore require `Count <= 2^29` on `MoveDown`, `RemoveRootNode`,
    `Dequeue`, `TryDequeue`, `DequeueEnqueue` and `EnqueueDequeue`.
  * `GetFirstChildIndex` requires `0 <= index < 2^29`.
* **`PriorityQueue.Enqueue`** requires `Count < int.MaxValue`, so that `_size + 1` cannot
  wrap. In practice `Grow` throws first, at `Array.MaxLength`.
* **`List.FindIndex`/`FindLastIndex` with a window.** The BCL checks the window before it
  checks `match`, so a bad window with a `null` `match` throws
  `ArgumentOutOfRangeException`, not `ArgumentNullException`. The `[Throws]` clauses are
  stated in that order. `FindLastIndex` on an empty list accepts `startIndex == -1` (and
  only that), with `count == 0`. Its ensures say so.
* The heap property is a precondition, not an invariant. Every member that needs it
  (`Peek`, `Dequeue`, `Enqueue`, …) requires it, and every member that changes the nodes
  re-establishes it.
* `_version` is not modelled, for either collection.

### 26.3 What is verified, and what is not

* **`List<T>`.**
  * Every member in §22 is verified.
  * The delegate members are verified: `Exists`, `Find`, `FindAll`, `FindIndex`×3,
    `FindLast`, `FindLastIndex`×3, `ForEach`, `RemoveAll` and `TrueForAll`.
  * So are `BinarySearch`×3, `Sort()`, `Sort(IComparer)` and
    `Sort(int, int, IComparer)`.
  * `ConvertAll`, `GetRange` and `Slice`, which build a second `List` by writing its
    private fields, are verified since §33 (R33.28).
  * These are not annotated:
    * `AddRange` and `InsertRange` take an `IEnumerable<T>` and dispatch on
      `ICollection<T>` through interface calls that the translation does not have;
    * `Sort(Comparison<T>)` goes through `ArraySortHelper` over a `Span<T>`;
    * the enumerators.
* **`PriorityQueue<TElement,TPriority>`.**
  * These are verified: `Count`, `Capacity`, `Peek`, `TryPeek`, `Clear`, `EnsureCapacity`,
    `TrimExcess`, `Grow`, `Enqueue`, `Dequeue`, `TryDequeue`, `DequeueEnqueue`,
    `EnqueueDequeue`, `RemoveRootNode`, `GetParentIndex`, `GetFirstChildIndex`,
    `MoveUpDefaultComparer`, `MoveUpCustomComparer`, `MoveDownDefaultComparer` and
    `MoveDownCustomComparer`; since §33 (R33.27) also `FindIndex` and `Remove`.
  * These are not annotated:
    * the constructors, because `InitializeComparer` tests `typeof(TPriority).IsValueType`
      and the `IEnumerable` constructors enumerate;
    * `EnqueueRange` and `Heapify`, which use `IEnumerable` and `ICollection` dispatch;
    * `UnorderedItems` and the enumerator;
    * the `Comparer` property, which returns `Comparer<T>.Default` for a null comparer;
      that is a value the model has only as a ghost.
  * The default-comparer and custom-comparer sift loops are verified separately. Both are
    specified at `comparer ?? Comparer<TPriority>.Default`.

## 27. `SortedSet<T>`: regions of tree nodes

`SortedSet<T>` is a red-black tree. Its `Node` class is linked by `Left` and `Right`, and
insertion and removal re-link nodes top-down, through pointers held in several locals at
once (`parent`, `grandParent`, `greatGrandParent`, `sibling`). Owning each node through its
parent, as R10 does for a recursive class, cannot follow that: a node is reachable from two
locals at the moment it is re-linked. This section therefore owns all the nodes of one
structure as one *region*. The nodes are cells of a ghost heap that the owner holds. The tree
a pointer reaches is a pure function of that heap.

Its library is `Pulse.Lib.CSharp.Region`. Its searches are in `Pulse.Lib.CSharp.SearchTree`.
The tests are `test/sortedset` and the `Region*` cases in `test/diagnostics`.

### R27.1 Verification at the exact type

Under `[TranslateAnnotatedOnly]`, a concrete generic class that is not `sealed`, and whose
every subclass in the compilation is untranslated, is translated as a leaf. This holds even
when it declares virtual members. (`SortedSet<T>` has `TreeSubSet` as a subclass, which
nothing annotates.) The untranslated subclass is not collected at all.

Why this is sound:

* The invariant is produced only by the class's own translated constructor.
* That constructor runs only for a translated `new C(...)`. A subclass's constructor chains
  to the CLR's constructor, never to the translation.
* So every receiver that verified code holds has dynamic type exactly `C`. Every virtual
  call on it binds to `C`'s own body.

What verified code cannot do is accept a `C` from unverified code. That code could hand it a
`TreeSubSet`. The contracts are claims about `SortedSet` objects only.

### R27.2 The null comparer

`IComparer<T>` is a reference type, so `default` at a comparer type is `null`. The model has
one value for it: `Comparer.null_comparer`, of which `Sorted.is_null` holds.

*Trusted:* `Pulse.Lib.CSharp.NullComparer.null_comparer` asserts that such a value exists.

### R27.3 `[Region]` classes

A `[Region]` class must have this shape:

* It is `sealed` and derives from `object`. Otherwise PALCS0700 is reported. A region holds
  one record type.
* It declares exactly two nullable fields (or auto-properties) of its own type. In declaration order, these are
  the left and right children. Otherwise PALCS0701 is reported.
* It has at most one `[Model]`, which must be an expression-bodied property. This is the
  *view* of one node. Otherwise PALCS0702 is reported.

It is emitted like a `[Plain]` class (R12): the record, `class_K__opt`, and the field
projections. It also gets the following:

| Pulse | meaning |
|---|---|
| `class_K__left r`, `class_K__right r` | the two child fields of a record |
| `class_K__view x r` | the `[Model]` of the node `x` holding `r` |
| `class_K__tree h x` | `Region.tree_of view left right h x`, the `Tree.tree` reached from `x` |
| `class_K__wf h x` | `Region.wf left right h x`: every path from `x` ends at `null` within the heap |
| `fn class_K__read x` | reads a node of the region (R27.5) |

The class has no methods of its own. Its constructor and members are not translated, and
`HasModel` is false for it. Nested in a generic class, it takes the outer type parameters as
well.

### R27.4 The owner holds the region

A class with a field of a `[Region]` type `K` is an owner. Its invariant gains three things:

* an existential heap `heap_K`;
* the resource `Region.region #raw #p heap_K`;
* for each such field `f`, the conjunct `class_K__wf heap_K r.f`.

In the owner's `[Model]` and in its contracts, `Pal.Tree<V>(f)` is `class_K__tree heap_K f`.

An owner is never split. `Pal.Share` and `Pal.Gather` are not emitted for it, because two
halves would hold two heaps that nothing proves equal.

### R27.5 Reading and writing a node

* **Reading.** A field read `x.f`, where `x` is of a region type, is
  `(class_K__read x).fld_f`. `read` requires `mem h x`, or `wf h x` and a non-null `x`. It
  ensures `mem h x` and that the record is `get h x`. When `wf h x` holds, it also ensures
  `Region.wf_step`: both children are well formed, and the tree at `x` is
  `Branch (tree left) (view x r) (tree right)`.
* **Writing.** `x.f = e` reads the record and then writes `{ r with f = e }` back through
  `Region.write`.
* **In a loop.** A loop's frame holds the region:
  * If the body writes no region field, allocates nothing and calls nothing, the heap is
    fixed across the loop, and the invariant may speak of `Pal.Tree` at that heap.
  * Otherwise the heap is existential.

### R27.6 Allocation, the empty region, and `default`

* `IrAlloc` of a region class is `Region.alloc`. It returns a fresh box, and the heap gains
  one cell.
* An owner's constructor creates the empty region (`Region.empty`) before it folds the
  invariant. An unassigned region field starts at `B.null`.
* `default` at a region type is `B.null`, typed so that a mutable local initialised with it
  can be allocated.
* `new Node(...)` is `Region.alloc` of the record its constructor builds (R27.16), as an
  expression and as a local's initialiser alike.

### R27.7 `Pal.Tree` and `Pal.WellFormed`

`Pal.Tree<V>(x)` is the `SpecTree<V>` that `x` reaches. `Pal.WellFormed(x)` says that `x`
is closed in the heap. Both are functions of the heap that the method holds, which is
`$heap_K` in scope. Their argument must be of a `[Region]` type; otherwise PALCS0703 is
reported.

A loop over a region names the tree at the cursor: `Pal.Decreases(Pal.Tree<V>(c).Size)`,
with `Pal.Invariant(Pal.WellFormed(c))`.

### R27.8 Reference equality

The heap is an association list from boxes to records. Looking up a box needs equality of
boxes to be decidable.

*Trusted:* `Pulse.Lib.CSharp.RefEq.ref_eq` is C#'s reference `==`. It decides box equality,
and that is the only fact it states.

### R27.9 Search specifications

`PalLang.SpecSearchTree` (`Pulse.Lib.CSharp.SearchTree`) specifies searches over a
`SpecTree<(T, TTag)>`:

* `Contains` and `Find` are the comparer-directed search;
* `Leftmost` and `Rightmost`;
* `HeapIndex`, the breadth-first position `2k+1` / `2k+2` that `InternalIndexOf` computes.

Each one follows the path the code follows, so it needs no ordering hypothesis. A search is
specified as *what this search returns*, whatever the tree. R27.11's model invariant
equates that with set membership.

### R27.10 The measure of a loop that returns

R26.2's `return` inside a loop sets a flag, and the rest of the body runs under
`if (not returned) { … } else { () }`. When Pulse joins the two arms, the skipped arm
contributes no fact. In particular it does not say that the cursor is unchanged, so after
the join the cursor of a returning iteration is unconstrained. Two consequences follow:

* R5.10's measure is `CA.until_set !brk m`, which is `0` once the flag is set and `m + 1`
  before. So the returning iteration decreases the measure whatever the cursor's state.
* An invariant about the cursor is guarded by `!Pal.Returned()`:
  `Pal.Invariant(Pal.Implies(!Pal.Returned(), Pal.WellFormed(current) && …))`.

### R27.11 The set-level model

A `SortedSet` is a set, not a search tree. The model therefore states what makes the tree a
set, as `[Refine]`s on the `[Model]`:

```csharp
[Refine("Pal.StrictlySorted(@this.Comparer, SpecSearchTree.Keys(@this.Tree))")]
[Refine("SpecSearchTree.IsRedBlack(@this.Tree)")]
[Refine("@this.Count == @this.Tree.Size")]
```

`SpecSearchTree.Keys` (`SearchTree.keys`) is the in-order sequence of the tree's items, and
`IsRedBlack` (`SearchTree.red_black`) is the red-black shape: a black root, no red node with
a red child, and equal black height on every path. The spec property
`SpecItems => SpecSearchTree.Keys(Model.Tree)` names the set. Every contract is stated over
it and over `Pal.KeyIndex`, so a client never sees the tree.

The bridge between the path-following searches of R27.9 and the set is proved in
`Pulse.Lib.CSharp.SearchTree`, without admits:

| lemma | statement |
|---|---|
| `sorted_branch` | a strictly sorted in-order sequence sorts both subtrees, with the pivot between them |
| `lower_bound_pivot` | `lower_bound` of `keys (Node l v r)` is that of `l`, `|keys l|`, or `|keys l| + 1 +` that of `r` |
| `find_keys` / `contains_keys` | on a sorted tree, `contains c t x <==> key_index c (keys t) x >= 0`, and `find` returns that key |
| `leftmost_keys` / `rightmost_keys` | `leftmost t` is `keys t` at `0`; `rightmost t` is at `|keys t| - 1` |

Several are `SMTPat`-triggered, so a method's proof needs no explicit lemma calls.

### R27.12 A contract on a `get` accessor

R9.20 read a computed property's contract only from the property. An attribute on its `get`
accessor was ignored without any message, and that contract was then never proved. Now:

* a contract written on the `get` accessor is read from the accessor;
* a contract written on both the property and its accessor is refused with PALCS0704.

For a property with a setter, R22.13 already read the accessors.

This was not hypothetical. In the `SortedList` sample, the contracts on the `Comparer` and
`Count` accessors had been dropped. Both are now proved.

### R27.13 Contracts that name the owner's heap

A method of a region owner may need to promise something about a region pointer it returns or
receives. `FindNode`, for example, returns a node a caller then reads. Such a promise is a fact
about the owner's *current heap*, which R27.4 keeps existentially quantified inside the owner's
invariant. R27.13 makes that heap nameable.

* `Pal.Tree<V>(x)`, `Pal.WellFormed(x)` and `Pal.InRegion(x)` inside a contract of an
  instance method of the owner resolve to `$heap_K` of `this`: the owner's heap for region
  class `K`. `Pal.InRegion(x)` is `Region.mem $heap_K x`.
* A method whose contract mentions `$heap_K` is *heap-indexed*. Its receiver is owned through
  `class_C__inv_heap this m heap_K…`, which has the same body as `class_C__inv` with the heaps
  as parameters. The method takes ghost binders `#pre_heap_K`. If the receiver is mutated,
  its post also binds `post_heap_K`. The contract's `$heap_K` is the pre heap in `requires`
  and the post heap in `ensures`.
* The class module emits ghost `class_C__to_heap` (`inv` to `exists* h. inv_heap … h`) and
  `class_C__of_heap` (back). At a call site the caller's form of the receiver is converted to
  the callee's form, and converted back afterwards. When the receiver is open (R22.15), it is
  closed, called and reopened at the heap the callee returns. So the facts the callee ensures
  about that heap reach the caller's opened region.
* A read of a field of a region object, inside a method of its owner, opens the receiver, as
  a read of the receiver's own field does.

Two `SearchTree` helpers serve the searches. `root_key t d` (`SpecSearchTree.RootKey`) is the
key at a tree's root. `find_keys_pat` gives `find` on a sorted tree as `keys t` at `key_index`
under an `SMTPat`.

### R27.14 Breadth-first positions and range search

`InternalIndexOf` computes a breadth-first position: the root is 0, and the children of `k`
are `2k+1` and `2k+2`. `SearchTree.heap_index` is that search, and its true bound is stated
through the tree's height:

| function / lemma | meaning |
|---|---|
| `breadth t` (`SpecSearchTree.Breadth`) | `2^height t` |
| `index_room k t h` (`IndexRoom`) | `(k + 2) * 2^height t <= 2^(h+1)`: positions below `k` in `t` stay at most `2^(h+1) - 2` |
| `index_room_step` | descending to a child preserves `index_room` with the child's position, and bounds `2k+2` |
| `index_room_int` | for `h <= 30`, the next position `2k+2` of a non-empty subtree fits an `int` |
| `heap_index_bound` | `heap_index c t x 0 >= 0 <==> contains c t x`, and it is at most `breadth t - 2` |

`FindRange` is a top-down search that stops at the first node inside the active bounds.
`SearchTree.range_hit` (`RangeHit`) is that search's outcome, and `in_range` (`InRange`) is the
bounds test. `any_in_range c s lo hi la ua` (`AnyInRange`) says some item of `s` is in range.
`range_hit_any` proves, on a strictly sorted tree, `range_hit c t … == any_in_range c (keys t) …`.
The proof uses only the comparer's transitivity, and the lemma is `SMTPat`-triggered.

### R27.15 A returning loop body is in tail position

R5.8d emits a loop body as a *tail* when the loop has no `break`, `continue` or `return`. Each
arm of a final `if` is then checked against the invariant, instead of being joined first. A
loop that may `return` (or `break`) and has no `for` step is now a tail as well. The escape
guard of R5.8d already keeps the statements after an escaping one under the flag.

The case that needed it is `FindRange`. Its arms write different locals: one writes `current`,
the other the result and the return flag. They do so after an `&&` whose right operand reads
a node, which is an `if`-expression whose result carries a refinement. Pulse could not join
those arms ("cannot find witness"). In tail position no join is needed.

### R27.16 Members of a `[Region]` class

A method or property of a `[Region]` class is translated. It takes `this` as a region pointer,
and it holds the region `this` lives in: the heap is a ghost binder `$heap_K`.

* A member that writes no node, and calls no member that does, is *read-only*. It takes a
  fraction of the region and leaves the heap as it was. Every other member takes the whole
  region and returns it at a new heap. Which members write is computed as a fixpoint over the
  call graph.
* Its contract names the heap through `Pal.Tree`, `Pal.WellFormed` and `Pal.InRegion`
  (R27.7). In `ensures` these mean the post heap, and `Pal.Old(…)` means the pre heap.
* `x.F = v` on a region pointer, held in a parameter or in a mutable local, is
  `Region.write x ({class_K__read x with fld_F = v})`. A field read through any expression
  of region type (`Left!.Left`) reads through the region.
* An `if` whose arm allocates, writes a node or calls a member that writes one is split at
  the join (as R25.10 does): Pulse would otherwise generalise the heap afresh and forget what
  the arm proved about it.
* `new K(a, b)`, for a `[Region]` class whose constructor only assigns parameters to
  fields, is `Region.alloc` of the record those assignments build. Fields it does not assign
  are `null` or the default. Any other constructor body is PALCS0705.
* `x.P = v` on an auto-property `P` of a region class is the field write, as R3.4 reads `P`
  as its backing field. Its setter has no body, so there is no method to call.
* `Pal.Heap<K>()` in a ghost statement of a member that writes the region is the heap as it
  stands at that statement: the region is re-read there, as a `[Open]` owner method's ghost
  statements re-read the record (R27.23). It used to be the heap on entry, so a lemma called
  after `ColorRed()` was told about the wrong heap.

Two predicates describe a re-linking, both from `Pulse.Lib.CSharp.RegionTree`:

| C# | F\* | meaning |
|---|---|---|
| `Pal.Unshared(x)` | `unshared left right h x` | `x` is well-formed and the tree it reaches holds no box twice |
| `Pal.Reshaped(x, y)` (in `ensures`) | `reshaped left right h0 h1 x y` | every box outside the tree `x` reached in `h0` is unchanged, and the tree `y` reaches in `h1` is made of boxes of that tree and of boxes allocated since |

`Pal.Reshaped(null, y)` says `y`'s tree is entirely fresh, as for `ShallowClone`.

`unshared` is what makes in-place updates provable. Writing a node that is in no other part
of the tree changes only the subtree it roots, so the trees of the other parts survive. The
owner's invariant (R27.4) now requires its root to be `unshared`, not just `wf`.

`RegionTree` keeps the boxes of a tree as an explicit `ltree` (the tree of `(box, record)`
pairs). `tree_of` is `vmap view (ltree …)`. Its lemmas are `SMTPat`-triggered. Each fires on
the term the emitted code produces:

* `upd_outside` / `upd_node` fire on a write.
* `alloc_outside`, `alloc_node` and `alloc_leaf` fire on an allocation.
* `unshared_step` unfolds one node.
* `reshaped_trans` composes two re-linkings.
* `reshaped_child` re-grafts a child after a call that re-linked it. It gives the sibling
  and the parent's record unchanged and the new subtree disjoint from both. When the child
  did not move, it also gives the parent's new tree.

`Region.tree_of` and `Region.wf` are `opaque_to_smt`. With their recursive definitions
visible, Z3 unrolled them on every heap term and timed out on trivial goals. `wf_step`,
`tree_of_mem`, `wf_mem` and `wf_null` give their one-step equations instead.

`SpecSearchTree` names the node-level operations on a colour-tagged tree:

* `Recolor`;
* `RotateLeft`, `RotateRight`, `RotateLeftRight` and `RotateRightLeft`;
* `Split4` and `Merge2`;
* `Rotate` and `CanRotate`.

`SearchTree` proves that each preserves `keys`. `SpecTree` gains `Left`, `Right` and
`RootOnly`.

### R27.17 Closed enums: `NodeColor` and `TreeRotation`

An enum without `[SpecType]` is its byte (R22.2), and a byte has 256 values. `Color ==
NodeColor.Red` and `Color == NodeColor.Black` are then not complements, so `IsBlack` could not
be `!IsRed`. The runtime's two enums carry `[SpecType]` (R21.8):

* `NodeColor` is `SearchTree.node_color = Black | Red`;
* `TreeRotation` is `SearchTree.tree_rotation`, its constants renamed by `[SpecCase]`.

A field of either type holds a constructor. A comparison with a constant of a `[SpecType]`
enum, in a value position of a specification (a component of a view), is the constant's
discriminator (`Red? c`), a `bool`.

### R27.18 Child links in contracts

`Pal.LeftOf(x)` and `Pal.RightOf(x)` are the first and second child links of a region object
in the heap the method holds: `Region.link_at class_K__left $heap_K x`. A box the heap does
not hold has the link `null`, so the term is total, and `link_at_mem` gives `left (get h x)`
for a box it does hold.

Contracts compare references with them (`node == Pal.LeftOf(@this)`). In code, `a == b` on
two region pointers is `RefEq.ref_eq` (R27.8). A null test on a region pointer typed
non-null is still a pointer test (`Debug.Assert(node != null)`).

A conditional whose test compares references (`x == y ? a : b`) needs decidable equality on
boxes in a specification. Write it as two `Pal.Implies` instead.

### R27.19 `Debug.Fail`

`Debug.Fail(m)` is erased along with its message under R22.19. It contributes no
unreachability fact. Use `Pal.Assert(false)` for a proof obligation at an unreachable point.

`Node.Rotate`'s `default:` arm is such a point. `TreeRotation` is closed (R27.17), so the
arm is unreachable.

### R27.20 A region pointer declared without a value

`Node removeRed;` is a cell of the nullable type, initialised to `null`. C#'s definite
assignment guarantees a write before every read. F\* proves the value read non-null from that
write, where the non-null type is needed.

### R27.21 `Pal.Heap<K>()` and `SpecHeap<K>`

`SpecHeap<K>` is the ghost type of the heap of a `[Region]` class `K`: F\*'s
`Region.heap (class_K__raw …)`, which maps a box to the record stored there. Two heaps compare
with `==`. `Pal.Heap<K>()` is the heap the enclosing method holds:

* in `requires`, and under `Pal.Old` in `ensures`, the heap on entry;
* in `ensures`, the heap on exit;
* in a ghost statement or a loop invariant, the heap at that point.

`Ghost<SpecHeap<K>> h1 = Pal.Heap<K>();` snapshots an intermediate heap, so that a ghost step
can relate two heaps of the same body. In a method of a region's owner, `Pal.Heap<K>()` is
the owner's heap (R27.13).

`Pulse.Lib.CSharp.RegionPath` carries the reasoning that relates heaps. A tree of boxes is a
*focus*: the path of frames from the root down to one node, and the subtree at that node. A
method that re-links the tree under `x` (`reshaped h0 h1 x x`) changes the whole tree by
replacing the subtree at `x`. `graft` lifts the local change to the root's tree.

### R27.22 `[RegionOp]`: specification operations over a region

`[RegionOp("F")]` on a static method is `[SpecOp]` (R11.1) with three more leading arguments.
The method's first type argument must be a `[Region]` class `K`. The call is the F\* term `F`
applied to `class_K__view`, `class_K__left` and `class_K__right`, then to the type arguments
and the arguments. So a library predicate can walk a region's heap without knowing the class.

A `void` `[RegionOp]` is a lemma. Called as a statement, it is a ghost call of the F\* lemma.
A `bool` literal passed for a `bool` parameter is the F\* boolean `true`/`false`, not the
proposition `True`/`False`. A comparison passed for one (`order < 0`) is its F\* boolean.
A first type argument that is not a region class is PALCS0706. `Pal.Heap<K>()` at a `K` that
is not a region class is PALCS0707.

### R27.23 `[Open]` helpers

A helper that the owner calls in the middle of an update cannot take the owner's invariant:
the invariant does not hold there. `InsertionBalance` is one. It runs between a split and the
rotation that repairs it. `[Open]` on an instance method of a region's owner hands it the
receiver *open*:

* The receiver is the record of its fields (`class_C__raw`) in a reference, plus each
  region's heap. It is not `class_C__inv`. The method gives them back the same way, at
  whatever record and heaps it leaves.
* Its contract names the fields directly (`@this.root`, `@this.count`). `Pal.Old(@this.f)` is
  the field on entry. `Pal.Heap<K>()` is the heap (R27.21).
* The caller hands over the receiver as it holds it: an `[Open]` caller passes its record
  and heaps on, and an ordinary owner method unfolds its invariant around the call. The
  record the callee returns is the caller's from then on, so a write to `root` inside the
  callee is seen by the caller.
* A ghost statement inside an `[Open]` method sees the fields and heaps as they stand at that
  point, not as they stood on entry.

A `ref` parameter of region type (`ref Node parent`) is a cell holding the *nullable*
pointer, whatever the declared type. C# lets the method store `null` into it through a
null-forgiving `!`, and the runtime does (R27.28). A `[Requires("parent != null")]` states
the entry value's non-nullness.

### R27.24 A conditional whose arms move a region

`x = c ? f() : g()`, an assignment to a local where `f` or `g` writes the region, is
translated as `if (c) x = f(); else x = g();`, as R22.15 already does for a `return` or a
declaration. The R27.16 split at the join then applies, so the facts each arm proves about
the new heap survive. `InsertionBalance`'s `currentIsOnRight ? grandParent.RotateLeft() :
grandParent.RotateRight()` is the case.

### R27.25 A loop that moves the heap it measures

A `while` loop whose body re-links the region can still decrease a measure over that region.
The measure (`Pal.Decreases(SpecTopDown.Measure(…, Pal.Heap<Node>(), …))`) reads the heap
through `Region.current`. That is a ghost function that does nothing, but its `rewrites_to`
gives Pulse the heap the invariant holds at each check. When the owner's record is also
written in the loop, a field in the measure (`comparer`) reads `!this` the same way. A
measure over a heap the loop moves without either form is PALCS0001: the measure would
name a binder the loop has already generalised.

### R27.26 Top-down red-black insertion

`SortedSet<T>.AddIfNotPresent` inserts in one pass down the tree. It splits every 4-node on
the way, and a rotation (`InsertionBalance`) repairs the red-red pair that a split under a
red parent leaves. Three library modules prove it, with no admits:

* **`Pulse.Lib.CSharp.TopDown`** is the pure half, over a boxed tree of `(box, (key, red))`.
  * `cmp c k v` is the sign of `c.Compare(k, v)`. Only the sign is used.
  * `descent` is the loop invariant. The tree is a focus (R27.21) whose path is a valid
    2-3-4 descent to `current`: every frame turns the way the search for `k` turns,
    `parent` and `grandParent` are the first two frames, and two facts carry the shape. If
    the parent is red and `current` is about to be split, there is a grandparent, the
    parent's sibling is black and `greatGrandParent` is the third frame. If `current` is
    red and its next node will be split, its sibling is black. `ok` says the whole tree is
    a set of the original keys, red-black but for a possibly red root.
  * `step` is one iteration, `insert_leaf` the final insertion, and `measure` the
    lexicographic measure. The measure decreases on a split even when `current` does not
    move.
* **`Pulse.Lib.CSharp.TopDownHeap`** reads `TopDown` through the heap. `nodes view left right
  h x` is the boxed tree that `x` reaches. Its props are what `Node`'s helpers ensure
  (`recolored`, `split4ed`, `rotated`, `relinked`, `replaced`). Its lemmas are the loop's
  ghost steps (`start`, `at_cur`, `look`, `split`, `after_balance`, `finish`). A few
  `SMTPat` lemmas cover facts that the emitted code produces but no ghost step names:
  * `inserted_empty`, the empty set's insertion;
  * `balance_pre_nonnull`, that `InsertionBalance`'s parent and grandparent are non-null;
  * `size_succ`, that `count + 1` fits when `count < int.MaxValue`.
* **`PalLang.SpecTopDown`** is the C# surface. Each member is a `[RegionOp]` (R27.22) over
  `TopDownHeap`. `Inserted(c, s, k)` is `s` with `k` inserted at `Pal.LowerBound(c, s, k)`.

`AddIfNotPresent`'s loop carries `SpecTopDown.Inv(comparer, k0, item, Pal.Heap<Node>(), root,
current, parent, grandParent, greatGrandParent, order)`. The body calls one ghost step per
program step. The result is the set-level contract of 27.2.

### R27.27 A loop body that returns from inside a region-moving `if`

In a loop body (R27.15), `if (order == 0) { …; return false; }` whose arm moves the region is
an escaping `if`. R22.12 joins it with the rest of the body under `if (not returned)`, and
the join would lose what the arm and the rest each know about the heap. So the rest of the
body moves into the `if`'s arms that do not end in a jump: the `if` becomes
`if (c) { …; return } else { rest }`, and there is no join to lose facts at.

### R27.28 `[AllowNull]` on a parameter

`[System.Diagnostics.CodeAnalysis.AllowNull]` on a parameter of non-nullable class type gives
it the nullable type. `InsertionBalance(..., Node greatGrandParent)` is called with a `null`
great-grandparent when the parent is the root's child. The runtime's call sites write
`greatGrandParent!`, and that `!` is not true. Without the attribute, the parameter's
declared type would be a promise the caller cannot keep. The attribute is inert in C#, and
nullable analysis already honours it.

### R27.29 `x?.M()` and `x?.F = v` as statements; re-assigned region parameters

A statement `x?.M()` or `x?.F = v` whose receiver `x` is a region pointer (a local, a
parameter or a field read, with no effect) becomes `if (x != null) { x.M(); }` (resp.
`{ x.F = v; }`). Inside the arm, the bound `.M()` / `.F` takes `x` as its receiver; a call
bound by `?.` used to take `this` instead, which was a bug. An effectful `x` is refused
(PALCS0001), since it would be evaluated twice.

A by-value region-typed parameter that the body assigns (`successor = match.Left`) is a
mutable cell, initialised from the argument (`let mut var_x = arg_x`). Only a direct
assignment `x = e` counts: passing `x` to a call or writing `x.F` does not make it a cell.
The contract still names the argument.

### R27.30 Top-down red-black removal

`SortedSet<T>.DoRemove` removes in one pass down the tree. It makes every node it reaches
not a 2-node, before it steps below it:
* the root is turned red;
* a red sibling is rotated up;
* two 2-node siblings are merged;
* a 2-node next to a 3- or 4-node borrows from it by a single or double rotation.

Once it meets `item`, it goes on to the match's in-order successor (the leftmost node of the
right subtree). At the bottom, `ReplaceNode` puts the successor in the match's place. Four
library modules prove it, with no admits:

* **`Pulse.Lib.CSharp.TopDownRemove`** is the pure half, over `TopDown`'s boxed trees.
  * `rinv` is the loop invariant. The tree is a focus whose path is the search for `item`,
    going right at a key equivalent to it. `match`/`parentOfMatch` are where the search met
    `item`. The node above `current` is not a 2-node.
  * `rmid` is the state after a red sibling is lifted, and `rfx` the state after the
    fix-up, when `current` is not a 2-node.
  * `removed c s k` is `s` without the element at `Pal.KeyIndex(c, s, k)`, or `s` when there
    is none.
* **`Pulse.Lib.CSharp.TopDownSucc`** is the end of the descent. `rdel` replaces the match by
  its successor, and `end_found` proves that the result is `removed` and is red-black.
* **`Pulse.Lib.CSharp.TopDownRemoveHeap`** reads the two through the heap.
  * `rinvh`, `rmidh` and `rfxh` are the invariants at a heap.
  * `rmeasure` is the size of `current`'s subtree.
  * The lemmas are the loop's ghost steps: `r_start`, `r_at_cur`, `r_fix_root`, the
    sibling cases `a_*` (red sibling) and `b_*` (borrow), `r_merge`, `r_step` and `r_after`.
  * `rn_*` prove `ReplaceNode`, and `rot_single`/`rot_double` prove `Node.Rotate`.
  * The `SMTPat` lemmas `rn_writes_ne`, `rn_writes_eq`, `rn_color_upd` and `b_s2_upd` see
    through the nested `upd`s that a node's successive writes leave.
* **`PalLang.SpecTopDownRemove`** is the C# surface. Each member is a `[RegionOp]` over
  `TopDownRemoveHeap`.

`DoRemove`'s loop carries `SpecTopDownRemove.RInv(comparer, k0, item, Pal.Heap<Node>(), root,
current, parent, grandParent, match, parentOfMatch, foundMatch)`. It decreases
`SpecTopDownRemove.Measure(Pal.Heap<Node>(), root, current)`. The body calls one ghost step
per program step.

`r_step` states the next node in two forms:
* as `if lt then left … else right …`, for the invariant;
* as `toward … o`, for the measure.

The `?:` the loop ends with is matched by the second form, and the `if (order == 0)` join by
the first.

`ReplaceNode` is `[Open]` (R27.23). It requires `SpecTopDownRemove.RnPre` (the match, its
parent, the successor and the successor's parent, as the descent leaves them). It ensures
`RnPost`: the root's tree is `TopDownSucc.rdel` of the old one at the match, which is the
match taken out and the successor moved into its place.

### R27.31 Discarded results; region-moving `if`s in a loop body

* An expression statement whose value is not `void` (`parent.RotateLeft();`) is
  `let _ = e;`. Pulse rejects a statement whose value is not `unit`.
* In a loop body (R27.15), an `if` whose arm moves a region (R27.16) is split as well. The
  rest of the body moves into both arms, as for an arm that writes the owner's record. The
  heap each arm leaves would otherwise be a fresh existential at the join, and what the arm
  proved about it would be lost. `DoRemove`'s `if (parent.Right == sibling)
  parent.RotateLeft(); else parent.RotateRight();` is the case. An escaping `if` keeps
  R27.27's treatment.
* A loop in a member that holds a region itself (a `[Region]` class's member, R27.16) or in
  an `[Open]` method (R27.23) carries that region's heap in its invariant, as an owner's
  loop does (R27.4). It is named once when the body writes no node, and is existential
  otherwise. In an `[Open]` method, `this.f` in the invariant is the field of the record
  the loop holds. Before this, such a loop dropped the region from its invariant, and the
  body could not touch a node.

### R27.32 Building a red-black tree from a sorted array

`SortedSet<T>.ConstructRootFromSortedArray(arr, startIndex, endIndex, redNode)` builds a
balanced tree over `arr[startIndex..endIndex]` in place. It puts the middle element at the
root, recurses on each half, and threads a red leaf (`redNode`) that an even-sized parent
saved down to the leftmost node of the left half. `Pulse.Lib.CSharp.SortedBuild` states and
proves what it builds:

* `build s lo hi red` is the tree the method builds, as a function of the array's contents.
  It is exposed as `SpecSearchTree.Build`. `red_arg` (`SpecSearchTree.IsRedLeaf`) says what
  may be passed as `redNode`: nothing, or a single red node.
* `keys_build` and `rb_build` give the keys (the slice, in order, with `red`'s key first)
  and the red-black shape. The black height depends only on the slice's length. `build_ok`
  (patterned) packages them for `red == Leaf`: keys are the slice, the tree is red-black,
  and its size is the slice's length.
* Heap lemmas for a body that only allocates and links fresh nodes. `alloc_fwd`, `upd_fwd`,
  `upd_left_child`, `tree_upd_node` and `tree_alloc_leaf` fire forward on the heap a step
  leaves, so no later goal has to name the intermediate heaps. `reshaped_outside`,
  `reshaped_box` and `reshaped_fresh_leaf` carry facts across a recursive call's
  `Pal.Reshaped`.
* Two `[RegionOp]` lemmas (R27.22), called as ghost statements in the default case:
  * `SpecSearchTree.LinkRight(h0, h3, red, root)`, with `h3` the heap once the left half
    is linked. Whatever heap `h5` and right root `y` the conditional `size % 2 == 0 ? …
    : …` produces (`Pal.Reshaped(null, y)` from `h3`, with `reshaped_fresh_leaf` folding
    in the allocated red node), linking `y` leaves `root` unshared, with
    `Tree(root) == Branch(left half, root's view, Tree(y))`, re-linking `red` since `h0`.
    The fact is stated at `h3` and quantified over what follows, so one call before the
    conditional covers both of its arms.
  * `SpecSearchTree.BuildSplit(items, lo, hi, mid, even, red)` is one step of `build`, at
    the midpoint and parity the code computed. Its region type argument is only there to
    make it callable as a lemma.

The contract:

```csharp
[Requires("0 <= startIndex && startIndex <= endIndex + 1 && endIndex < arr.Length")]
[Requires("arr.Length <= 1073741824")]
[Requires("Pal.Unshared(redNode) && SpecSearchTree.IsRedLeaf(Pal.Tree<(T, bool)>(redNode))")]
[Requires("startIndex <= endIndex || redNode == null")]
[Ensures("Pal.Contents(arr) == Pal.Old(Pal.Contents(arr))")]
[Ensures("Pal.Unshared(Result) && Pal.Reshaped(redNode, Result)")]
[Ensures("Pal.Tree<(T, bool)>(Result) == SpecSearchTree.Build(Pal.Contents(arr), startIndex, endIndex, Pal.Old(Pal.Tree<(T, bool)>(redNode)))")]
[Ensures("Pal.Implies(redNode == null, SpecSearchTree.IsRedBlack(Pal.Tree<(T, bool)>(Result)) && SpecSearchTree.Keys(Pal.Tree<(T, bool)>(Result)) == Pal.Slice(Pal.Contents(arr), startIndex, endIndex + 1))")]
```

The array bound reflects a finding (27.3). The array's frame must be stated: without it the
post leaves the array's contents unconstrained.

The ghost statements in the body are arithmetic asserts that keep the case analysis cheap,
`Pal.Assert(Pal.Unshared(root))` after each round of links, and the two lemma calls. `size
% 2` as the code computes it (`I32.rem`) is linked to the specification's parity by
`SortedBuild.rem2`.

### R27.33 Writing a field of a field

`root.Left.Left = redNode` writes a field of a region object that the receiver expression
reaches. The receiver is a pointer value like any other. It is evaluated first (a read of
`root`, then of its `Left`), as C# evaluates it, and the write goes through the result as
R27.5 does. Before this, only a field of a local could be written.

### R27.34 A conditional whose arms move a region, assigned to a field

R27.24's split also applies to an assignment to a field of a local, `v.f = c ? f() : g()`.
C# reads `v` before either arm runs, and no call can assign a local, so reading it in each
arm is the same. `ConstructRootFromSortedArray`'s `root.Right = size % 2 == 0 ?
Construct(…, new Node(…)) : Construct(…, null)` is the case. Joined as one expression, the
arms' differently allocated heaps leave Pulse a `match` on the condition that it cannot
reduce.

### R27.35 Collections of pointers into a region

A `[Region]` class can be a type argument of an ordinary class (`Stack<Node>`,
`PtrStack<WNode>`), an array element type, or a `Seq` element type. Its image there is
the nullable box `class_K__opt`, which is the pointer as a value (R27.3). C# lets a
`Stack<Node>` hold the `Node?` that `Pop` might return, so the nullable box is the right
image. Boxes get a `has_default` instance (`B.null`), so a generic collection can take
`default(T)` at one.

What the stack holds is plain data, so its model is a `Seq` of pointers. Any claim about
those pointers, for example that each is in the region or that together they still owe
certain keys of the tree, is a pure statement about the heap the owner holds.
`Pulse.Lib.CSharp.RegionWalk` (C# surface `SpecWalk`) states the claims an in-order walk
needs:

* `Keys(rev, t)`: the keys of `t` in order, or in reverse.
* `Pending(rev, h, s)`: what the stack `s` still owes in `h`, with the top (the last
  element) first. Each entry owes its key and then the keys of its far subtree.
* `Walkable(h, s)`: every entry is non-null and well-formed.
* Lemmas:
  * `Empty`;
  * `Descend`: push `x`, move to its near child;
  * `Pop`, and `PopAt` for a stack that owes a window `ks[n..]`;
  * `Length`.

`test/sortedset/Walk.cs` uses an array-backed `PtrStack<WNode>` and verifies that an
iterative in-order walk counts every node and copies the keys out in order.

### R27.36 A call to a method that holds no region

A method of the owner calls region-free code mid-traversal, such as `stack.Push(node)`.
R27.16 used to assume such a callee might write the region, since it was not known to
leave it alone. A loop around the call then re-quantified the heap, and so lost what
the invariant said about it. Now a method whose body names no region and calls only
methods that are themselves region-free (transitively) holds no region. A call to it
neither reads nor writes the caller's region.

### R27.37 A borrowing struct that owns an object

R28 lets a struct borrow its owner (`_tree`) and hold plain fields. An enumerator over a
tree also holds a stack of pointers that it allocated itself (`_stack = new
Stack<Node>(…)`). That object belongs to the struct, not to the owner.

* **Owned field.** A `readonly` class-typed field of a borrowing struct is *owned* if:
  * it is not the owner field;
  * its class has a model; and
  * its class is not a `[Region]` class.

  A region-class field (`_current`) is a pointer, which is plain data (R27.35).
* **Members.** Each member takes one extra object parameter per owned field,
  `__pal_own<f>`, after `self`. It holds the object's invariant before and after (R4.10).
  Its contract gains `self.f == __pal_own<f>`, required and (for writers) ensured. In a
  contract or body, `this.f` denotes that parameter, so `_stack.Items` is the stack's
  model.
* **Frame facts.** A writer's frame facts are stated unconditionally, outside R4.8's
  `PRE ==> POST`: the owner and owned fields keep their objects, and `readonly` fields
  keep their values. They are well typed without the precondition.
* **Writer self-calls.** A member may call a writer member of the same struct
  (`Reset` calls `Initialize`). The call passes `self` by reference and the owned
  objects. Whether a member writes is transitive over such calls.
* **Constructor.** A constructor may initialise an owned field with a constructor call
  and end with calls to its own members (`Initialize()`).
  * Field values that contain calls are let-bound first, in source order.
  * The struct is then built in a cell, and the trailing calls run on it.
  * The cell is returned.
  * The postcondition hands over each owned object as `exists* m. inv (result.f) m`,
    and `Result.f` in its contract denotes `m`.
  * At the return, the local's invariant is rewritten to the field's, since they are
    the same reference.
  * The same applies to an owner method that returns such a struct (`GetEnumerator`).

A client that *holds* such a struct and calls its members is not supported. This
includes `foreach` over it and an `IEnumerator` box. The members are verified, but the
call site does not yet thread the owned objects. `test/sortedset/Walk.cs` verifies
`WalkSet<T>.Enumerator`, an in-order or reverse walk over a `PtrStack<WNode>`:

* `MoveNext` yields the next pending key.
* `Reset` starts again.
* The constructor and `GetEnumerator` leave the whole in-order (or reversed) key
  sequence pending.

### R27.38 Translating the runtime's enumerator

`SortedSet<T>.Enumerator` in the runtime source needs several small rules beyond R27.37.

* **Chained borrowing constructors.** A borrowing struct's constructor whose body is
  empty and whose initializer is `: this(…)` is the call of the target constructor. Its
  owner parameter is the target's, through the argument passed for it.
* **`[Wrapping]` on constructors.** R21's `[Wrapping]` may mark a constructor. The
  enumerator sizes its stack as `2 * Log2(TotalCount() + 1)`, whose `+ 1` may wrap at
  `int.MaxValue`, harmlessly.
* **Omitted optional arguments.** A call that omits an optional parameter whose default
  is a `bool` or integer constant passes that constant (`VersionCheck()` is
  `VersionCheck(false)`). Only positional arguments are supported.
* **Multiple declarators.** `Node? next, other;` declares both locals in the enclosing
  block, not in a nested one.
* **Owner methods that keep their heaps.** An owner's method is held at its heaps
  (R27.13) and gives them back unchanged when all of the following hold:
  * no value of a region class appears in its body, parameters, return type or locals;
  * every call it makes on an object is a call on `this` to another such method (a
    greatest fixpoint over the call graph);
  * its contract does not name a heap; and
  * it is not `[Open]`, a constructor or an override.

  `IsWithinRange`, `VersionCheck`, `Count` and `TotalCount` are such methods. A caller
  part-way through a traversal therefore keeps what it knew about the region across the
  call, and a loop that calls one keeps its heap named (R27.31). Soundness does not rest
  on the test: each body is verified against the signature it selects.
* **Calls that may raise.** A call to a method with a `[Throws]` hands its exception, with
  everything the caller holds, to the caller's `raises` clause, which owns the closed
  objects. Before such a call, every open object held read-only (a borrowing struct's
  owner) is closed at its model. After the call it is reopened at the same model, which
  the call could not change.
* **Throw guards.** In `if (c) throw …;` followed by more statements, the rest of the
  block becomes the `else` arm. Pulse's join of the two arms would otherwise forget `!c`.
* **Loops that reopen an object.** A loop body that closes and reopens an open object
  gets a fresh record at each reopening. This happens with a self-call (R22.15) or with
  the raising bracket above. The loop invariant therefore quantifies that record
  existentially; it cannot name the record from before the loop. If the object is held
  read-only and its class has no array or object fields, the invariant also states
  `class_C__abs r heaps m`. That is the pure half of the class invariant, which is what
  folding the object back at its model needs. The class module defines `class_C__abs`
  for such classes.

The runtime `SortedSet<T>.Enumerator` is verified with these rules (27.2). It uses the
runtime's own verified `Stack<T>` as its stack of region pointers (R27.35), and
`BitOperations.Log2` is a trusted binding (27.1).

### R27.39 Lambdas passed to a callback over a region

A delegate parameter marked `[Callback]` takes a pointer into a region its method holds:
```csharp
internal delegate bool TreeWalkPredicate<T>(SortedSet<T>.Node node);
internal virtual bool InOrderTreeWalk([Callback] TreeWalkPredicate<T> action) { … }
```
The parameter's type must be a delegate with one non-`ref` parameter, of a region class
with a `[Model]`, and a non-`void` result. Anything else is PALCS0708.

**The callee.** The delegate is `Callback.region_cb view p`, together with the caller's
protocol `p : Seq.seq (v & r) -> slprop`. Here `v` is the region class's view and `r` the
result. A call `action(x)` needs `x` non-null and in the heap. It takes `p tr` and the
region, at any fraction and heap, and gives back the region unchanged and
`p (snoc tr (view x, result))`. So a call never writes the region (R27.5), and a loop that
calls back keeps its heap named.

In the callee's contract, invariants and ghost code, `Pal.Trace<V, R>(action)` names `tr`:
* its precondition holds `p` at the empty trace;
* its postcondition holds `p` at an existential trace, which is the one its ensures
  mention;
* in a loop the trace is carried like a cell, and a `decreases` reads it with
  `Callback.trace_now`, as `Region.current` reads a heap.

Nothing is said of what `action` does. `RegionWalk.walked keys tr res` says that the walk
called back on the keys in order and stopped at the first `false`:
* `res` is true and every call returned true, with `tr`'s keys exactly `keys`; or
* `res` is false and `tr`'s keys are a prefix of `keys` whose last call alone returned
  false.

**The caller.** A lambda passed for a `[Callback]` parameter is a block whose first
statement states its protocol:
```csharp
InOrderTreeWalk(node =>
{
    Pal.Protocol<(T, bool), bool>(tr => SpecWalk.Copied(tr, a0.Value, Pal.Contents(array), i0.Value, count, index));
    …
});
```
The lambda is lifted to a method of the enclosing type, `{Method}_Lambda{n}`. Its
parameters are, in order:
1. the trace, ghost;
2. its captures, in source order. A local the lambda writes is passed by reference, and an
   array by its contents. A `Ghost<T>` capture is ghost, with machine integers read as
   `SpecInt`;
3. the node, at the region type.

The lifted method requires the protocol at `tr` and the node in the heap. It ensures the
protocol at `snoc tr (view node, Result)`. It is verified as any other method, holding the
region read-only.

Two wrappers follow it:
* `protocol_L caps tr` is the protocol as an slprop: the captures' resources at existential
  values, and the formula;
* `callback_L caps` is a `region_cb` that unfolds the protocol, calls the lifted method,
  and folds the protocol at the extended trace.

At the call site the caller folds `protocol_L caps` at the empty trace and passes
`protocol_L caps` and `callback_L caps`. After the call it unfolds the protocol at the
trace the callee ensures, so the captured locals and arrays come back with what the
protocol says of them.

A lambda that does not start with `Pal.Protocol`, or that captures `this` or an object (but see R27.40), is
refused (PALCS0709).

This is sound because the callee is verified against every protocol: `p` is a parameter,
and the only access it has to `p` is through the callback. The caller supplies a callback
that keeps its own protocol. Nothing is trusted.

**Conversions to `SpecInt`.** R13.2 read a conversion from a machine integer to `SpecInt`
as a truncation, because `SpecInt` has no width. `(SpecInt)index` was `index % 2^32`.
Every machine integer is a `SpecInt`, so the conversion is now the identity. No earlier
contract relied on the truncation.

The runtime's `InOrderTreeWalk` and its three `CopyTo` overloads are verified with this
rule (27.2). The walk's stack is the runtime's own `Stack<Node>` (R27.35). `Count + 1` in
its capacity may wrap, so the method is `[Wrapping]`, like the enumerator's constructor
(R27.38). `CopyTo(array, index, count)`'s lambda writes the captured `index` and
`array`. `RegionWalk.copied_walked` turns its protocol and the walk's `walked` into
`CopyResult`: the first `min(count, Count)` items, in order, at `index`.

### R27.40 Breadth-first walks, captured objects and `RemoveWhere`

`RemoveWhere` collects the members `match` holds of into a local `List<T>`, from a
lambda passed to `BreadthFirstTreeWalk`, and then removes each. Verifying the pair needed
the following, none of it trusted.

**A bound on calls.** `Callback.region_cb`'s call now also requires
`Seq.length tr < max_calls` (`max_calls = 2^31 - 1`). The callee proves it before each call
(a walk calls back at most once per node, and an `int` counts the nodes), and the lifted
lambda may assume it. That is what lets a callback count its calls, or add to a list, in an
`int`.

**Captured objects.** A lambda may capture a local of a translated class that is non-null
(a `var` local is nullable in C#; declare its type) and owned in full. Its protocol holds
the object at an existential model, as an array is held at its contents (R27.39), so the
protocol can mention the object's specification members. Any other object capture, and
`this`, is still PALCS0709.

**Breadth-first walks.** `RegionWalk`'s second half is the queue's analogue of R27.35's
stack: `bpending heap q` is the keys the queue of pointers owes, front first, each node
followed by its children at the back. Its C# names are in `SpecWalk`:
* `BfPending(heap, q)`, `BfVisited(keys, tr, pending)`, `BfWalked(keys, tr, res)`;
* `BfStart(keys, tr, pending)` (a `[RegionOp]` lemma: an empty trace with the root queued
  is a visit), `BfDequeue(heap, q, keys, tr)` and `BfNext(heap, q)`, the queue after one
  step.

`bf_walked keys tr res` says: every call was on a member of `keys`, all calls but the last
returned true, a true result means every member was called on, and a false one that the
last call returned false. `bf_visited` and `bf_walked` are `opaque_to_smt`, revealed only
inside the library's lemmas. With them transparent, each Pulse query carried their
quantifiers, and the runtime's walk ran out of time after 11 minutes. Opaque, it verifies in
under a minute.

**`SetFilter`.** `Pulse.Lib.CSharp.SetFilter` (C#: `SpecSetFilter`) states the removal:
`removing c s0 s m i` says `m`'s elements past `i` were removed from the strictly sorted
`s0`, leaving `s`. `RemovingStart` and `RemovingStep` are its lemmas, and `FilterUnique`
turns the final membership into `s == Pal.RemoveAll(s0, match)`, since a strictly sorted
sequence is determined by its members.

**`void` `[SpecOp]`s are lemmas.** A `void` member with `[SpecOp]` is called as a ghost
statement, as a `void` `[RegionOp]` is (R27.22).

**Class indexers.** A read-only indexer whose `get` is an accessor, with its contract on
the accessor (R22.13), is collected as `get_Item`. A read `list[i]` in code is a call of it,
as a computed property read is (R9.20a). In full-translation mode, an indexer with a setter
or an expression-bodied indexer is still PALCS0591; this accounting restriction is separate
from R22.21's lowering of writes when the setter is translated.

**`ThrowIfNull` of a delegate.** A non-nullable delegate parameter is non-null (R10), so
`ArgumentNullException.ThrowIfNull(match)` is nothing, as it is for arrays and objects.

**Splitting `if`s in escaping loops.** Pulse joins the arms of an unannotated `if`, and
loses what the arms' calls ensured about a mutated object. R26.5 moves the rest of the
block into both arms in a loop that does not escape. Inside a loop that may `return`, it now
does so too for an `if` that does not escape itself and calls a method on a local object.

**`RemoveWhere`.** It ensures `SpecItems == Pal.RemoveAll(Old(SpecItems), match)` and
returns how many members it removed. It has no `[Throws]`. `match` cannot be null, and a
`[Throws]` clause would need the local `List`'s resources to be dropped on `get_Item`'s
raise path, which a raise clause cannot express (27.3).

### R27.41 An owner holds a borrowing struct

R28.6 refuses every call of a borrowing struct's member from verified code, since what the
call passes for the borrowed object is not designed. One case is designed now: an instance
method of the owner class holds a struct that borrows `this`.

```csharp
Enumerator e = new Enumerator(this, reverse: true);
while (e.MoveNext()) { … e.Current … }
```

**Where.** The local is declared in the method's top-level block (not in a nested block or a
lambda), its type is a borrowing struct, and its initialiser is `new S(…)` whose owner
argument (positional or named) is the literal `this`. Anything else is PALCS0710.

**Translation.** The struct's constructor returns the struct, which owns its own objects
(the enumerator's stack). The holder binds each owned object to a local
`__pal_own_<e><field>` and keeps its invariant, as a method of the struct does for its
fields. A call `e.M(args)` passes `this` (and its permission and heap) for the borrowed
object, the owned locals for the owned objects, and `e` by reference when `M` writes the
struct. A loop carries the owned objects at fresh models, and `this` at its fixed heap
while nothing writes it.

**Specification members.** A `[Spec]` property of the struct is an abbreviation. In a
contract or invariant of the holder, `e.SpecPending` is inlined with `e`'s fields and the
owned locals. It is never translated as a function. So `SortedSet.Enumerator` states the
state a holder needs as two:

```csharp
[Spec] internal Seq<T> SpecPending => SpecWalk.Pending<Node, T>(_reverse, Pal.Heap<Node>(), _stack.Items);
[Spec] internal bool SpecReady => SpecWalk.Walkable<Node, T>(Pal.Heap<Node>(), _stack.Items) &&
                                  SpecPending.Length <= _tree.SpecCount && _version == _tree.SpecVersion;
```

**Read-only.** A call of a borrowing member on a held local writes the struct (a local), not
the receiver. So it does not make the holder a writer of `this`, and a holder that only
enumerates keeps `this` at a fraction.

**Fail-fast.** `MoveNext` raises when the version moved. The holder knows the version is
`this`'s, which it holds and does not write, so the raise path is unreachable and the holder
needs no `[Throws]`.

**Loops (fixes).** The loop analysis now reads the loop condition for what it assigns and
mutates (`while (e.MoveNext())` writes `e` and its stack). A folded object with a heap is
carried at a fresh heap in a loop invariant, rather than as a plain `class_inv`.

### R27.42 Iterator methods

A method whose return type is `IEnumerable<T>` or `IEnumerator<T>` and whose body has a
`yield` statement is an iterator. C# compiles it to a state machine that runs the body
lazily, one `MoveNext` at a time. pal-csharp verifies the body as **one whole
enumeration**:

* the translation returns `Seq<T>`, the values yielded, in order;
* a local `__pal_yielded` starts at `Seq.empty`;
* `yield return x` is `__pal_yielded := Seq.snoc __pal_yielded x`;
* `yield break` returns `__pal_yielded`, inside a loop through R26.2's flag, and so does
  falling off the end.

`Pal.Yielded<T>()` names the trace. In the body (a loop invariant, an assertion) it is the
values yielded so far; in an ensures it is all of them. So `Reverse` is:

```csharp
[Ensures("Pal.Yielded<T>() == Pal.Reverse(@this.SpecItems)")]
[Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
public IEnumerable<T> Reverse()
{
    Enumerator e = new Enumerator(this, reverse: true);
    while (e.MoveNext())
    {
        Pal.Invariant(e.SpecReady && Pal.Concat(Pal.Yielded<T>(), e.SpecPending) == Pal.Reverse(this.SpecItems));
        Pal.Decreases(this.SpecItems.Length - Pal.Yielded<T>().Length);
        yield return e.Current;
    }
}
```

**Why one whole enumeration is sound.** The lazy body interleaves with its client: the
client runs between two `MoveNext`s. The whole-enumeration reading is what the client
observes when the interleaved code does not write what the body reads, and the body does
not write what the client reads. The second half is enforced (PALCS0712):

* the receiver is read-only (the body does not write `this`), and
* every parameter is a value (no array or object the body could share with its client).

So the body's writes are to its own locals: its trace, and objects it creates (the
enumerator and its stack). An enumeration stopped early has yielded a prefix of the trace.
The first half — the client does not write the collection while it enumerates — is the
assumption every enumerator makes (R28.8).

**Fail-fast.** Under that assumption, the version check in the body never fails, and the
translation proves it: the body's `MoveNext` calls need no `[Throws]`. A client that does
write the set mid-enumeration gets C#'s `InvalidOperationException` at its next
`MoveNext`, which this contract does not describe (27.3).

**Calls are refused.** A call of an iterator method from verified code is PALCS0711: what it
returns is an enumerable, which has no translation. The iterator is verified for its
contract; enumerating its result through `foreach` is a client feature not designed yet.

### R27.43 Cloning a region tree: `DeepClone`

`Node.DeepClone(count)` copies a tree without recursion. It keeps a
`Stack<(Node source, Node target)>` of pairs still to do. It pops a pair, clones each child of
`source` (`ShallowClone`), links the clone under `target`, and pushes the child pair. Four
small rules and one library make it translate and verify.

* **`out var` in a `while` condition.** `while (s.TryPop(out var next))` declares `next` in
  the condition. The declaration is hoisted to a local before the loop, so the guard writes
  it as any `out` argument does (R6.10).
* **Declaration patterns on a region class.** `if (e is Node x) S1 else S2`, with `e` of a
  `[Region]` class type, is `x = e; if (x != null) S1 else S2`. The test of a region pointer
  is its null test; no type test is involved, since a region class is sealed in the
  translation (R27.1).
* **Region pointers in tuples.** A tuple component of a `[Region]` class type is the
  nullable pointer (`class_X__opt`), as a generic argument already is (R27.35). So
  `(Node, Node)` has a default, and `Stack<(Node, Node)>` is a stack of plain values.
  Reading a field through a component needs the component's non-null fact, which the
  loop's ghost steps supply.
* **A measure that names a mutated object.** A loop's `Pal.Decreases` may name an object
  local the loop writes (`pendingNodes.Items`). The measure is evaluated at the top of the
  body and at its end, and binds the local to `Callback.model_now inv ()`: a ghost function
  that returns the model under the object's current invariant and leaves it in place. This is
  the object analogue of a heap's `Region.current`.

**The invariant: a tree with holes.** `Pulse.Lib.CSharp.RegionClone` (C# facade
`SpecClone`) states it. With `h0` the heap at entry, `src` the source root, `h` the current
heap, `dst` the clone's root and `st` the stack, `SpecClone.Cloning(h0, src, h, dst, st)`
says:

* every pending pair is a source node of `src`'s tree and a target node of `dst`'s, and
  each pending target is still a leaf of the clone;
* if the clone's tree had each pending target's subtree replaced by its source's subtree,
  it would be the source tree (`zip`);
* the sources are distinct; no target is a node of the source tree; and the source tree is
  unchanged since `h0`.

The ghost steps `Init`, `Pop`, `Link` (once per child, after the write and before the
`Push`), `Done` (after both children) and `Finish` (when the stack is empty) carry it
around the loop. `Finish` concludes that the clone is the source tree and is unshared.
`SpecClone.Measure` is `2 * (size - nz) + |st|`, where `nz` counts the source nodes whose
children are cloned; `Pop` and `Done` state how it moves.

So `DeepClone` ensures `Pal.Tree(Result) == Old(Pal.Tree(@this))`, `Pal.Unshared(Result)`
and `Pal.Reshaped(null, Result)`. It requires `Pal.Unshared(@this)` and
`Tree.Size <= count`. The size bound gives the stack's `Push` its `Count < int.MaxValue`
bound, since the stack never holds more than the tree's nodes. The initial capacity
`2 * Log2(count) + 2` is a hint: the runtime `Stack<T>` grows.

The library has no admits or assumptions. `test/sortedset/TopDownInsert.cs` verifies the
same loop over `RbNode`.

### R27.44 Two owners of one class

A method of an owner may read another object of its own class. `other.f` (a parameter or
local `other` of the receiver's class, outside a spec) is read through `other`'s own
invariant. The emitter opens `other` (`class_C__to_heap`, then `unfold class_C__inv_heap`)
around the read, and folds it again at the same model. Its heaps are named explicitly, so
the fold cannot pick up the receiver's region by mistake. `other` is held the way any
parameter of a class type is held (R4.9), so the method's contract still states only
`other`'s model.

**A call in the other owner's region.** A call that takes a region pointer read from
`other`'s field (`other.root.DeepClone(n)`, `Node.IsRed(other.root)`) runs in `other`'s
region:

* The emitter opens `other` around the whole call, so the callee's `region` is `other`'s.
* If the context holds the receiver's own region of the same class bare (the receiver is
  open, or the method is `[Open]` or holds the region), that region is *parked* first.
  `RegionMove.park` turns `region h` into `parked h`, which a region call cannot match.
  `unpark` restores it after the call. So one `region` of the class is in scope at the
  call.
* `other` is folded at the heap the call left. Its abstraction must hold there at the same
  model; that is checked, not assumed.

**Moving a fresh tree.** A call in `other`'s region that returns a pointer of the region's
class is taken to have built a fresh tree. The tree is moved into the receiver's region, so
the receiver can store it. `Pulse.Lib.CSharp.RegionMove.move` checks that the callee
ensured `Pal.Unshared(Result) && Pal.Reshaped(null, Result)`: the call touched no box
`other` held before it, and every box of the result's tree is new.

`move` splits the boxes of the result's tree out of `other`'s heap into the receiver's
(`moved_from`, `moved_into`). It ensures:

* the moved tree is the same tree, and unshared, in its new region;
* every unshared tree of `other`'s heap before the call is the same tree, and unshared,
  in what is left;
* every unshared tree of the receiver's heap is the same in the joined heap.

The last two are stated as quantified facts triggered on `unshared`/`ltree`, so the folds
of both owners' abstractions find them. The disjointness of the two heaps comes from the
full-permission cells (`apart`, by `Region.fresh`). No cell moves in memory; what moves is
ownership. The library has no admits or assumptions.

A move is attempted only when the receiver's region of that class is held bare. Otherwise
the result stays in `other`'s region.

`RbSet.CountOf`, `RootRed` and `CopyFrom` (`root = other.root.DeepClone(other.count)`) in
`test/sortedset/TopDownInsert.cs` verify these rules. `CopyFrom` ensures
`SpecItems == other.SpecItems`.

### R27.45 Constructor bodies after `: this(...)`

`C(…) : this(args) { S }` is no longer refused (it was PALCS0598, R4.12c). The chained
constructor's call comes first, and returns the object with its invariant folded at some
model. The emitter opens it there (`with m. assert (inv o m); unfold …`), and `S` is then
an instance method body over it: field writes, region calls and R27.44's peer reads all
work as in a method. The object is closed at the end against this constructor's own
`[Ensures]`, as R22.9's open constructor's is.

R4.12b's rule that a constructor consumes its object parameters is narrowed to a body that
may store the reference. A parameter used only as the receiver of field reads and method
calls, as an argument of a method none of whose parameters is `[Consumes]` or of a
constructor that hands that parameter back by this rule, or in a null test, is handed back.
So a copy constructor preserves its argument, and so does one that chains to it.

`RbSet(RbSet<T> other) : this(other.comparer) { … root = other.root.DeepClone(other.count); … }`
in `test/sortedset/TopDownInsert.cs` verifies both rules, together with R27.44's move.

A `return;` in the body returns the object: the emitter rewrites it to `return this`, and
appends `return this` to every path that falls off the end (both branches of a trailing
`if`). A `return` inside a loop or a `try` is still refused. `Cell(Cell other, bool skip)
: this(0)` in `test/sortedset/Exact.cs` returns early on `skip`.

### R27.46 A parameter that is exactly one class: `[Exactly(typeof(C))]`

`collection as SortedSet<T>` on an `IEnumerable<T>` parameter asks for the argument's
dynamic type, which the translation does not model. R27.1's argument gives a sound special
case. Every reference that verified code holds to a sealed (or effectively sealed, R27.1)
translated class `C` has dynamic type exactly `C`. So a parameter that every caller fills
with such a reference can be treated as a `C`:

* **The parameter.** `[Exactly(typeof(C))]` is accepted on a parameter when `C` is a
  non-abstract class with a model, sealed or effectively sealed, with an implicit
  reference conversion to the parameter's type. A generic `C<>` is closed by unifying its
  interfaces and base types with the parameter's type (`IEnumerable<T>` gives
  `SortedSet<T>`). The parameter is lowered at type `C`: it is held as a `C` (R4.9), and
  contracts may name its spec members.
* **The callers.** An argument at the parameter must have static type `C` and be non-null
  (it is not boxed). Anything else is PALCS0713.
* **Type tests.** On such a parameter `p`, `p is D` and `p as D` are decided from `C`:
  `p is D` is `p != null` when `C` converts to `D` and `false` otherwise, and `p as D` is
  `p` or `null` alike. `D? x = p as D;`, with `x` never written, makes `x` another name
  for `p`. `p == null` on a non-nullable class-typed value without effects is folded to
  `false`, so the dead branch drops out.

The callers that a verified contract leaves out — unverified code passing some other
`IEnumerable<T>` — are outside the verified reading, as every caller that breaks a
precondition is. `Cell.Read`, `IsCell` and `Client` in `test/sortedset/Exact.cs` verify
these rules.

### R27.47 Comparer identity and `Equals`

Two operations on `IComparer<T>` references had no model:

* **`==`/`!=` on two comparers** (outside a spec) is reference equality. It is lowered to
  `ComparerIdentity.same c d`, whose result is `c == d` on R22.30's comparer values. This
  is a modeling axiom: a comparer value stands for one object. It holds because the
  translation creates comparer values only as `Comparer<T>.Default` (one cached object),
  the null comparer (R27.2), or by receiving them, so it never gives two objects one value.
  Two distinct objects that order alike are distinct values; nothing says they are equal.
* **`c.Equals(o)`** (`object.Equals`, which a comparer class may override) is lowered to
  `ComparerIdentity.equals c (box o)`, an uninterpreted, deterministic function. Nothing
  else is assumed: in particular not that `Equals` implies the same order.

`HasEqualComparer` (`Comparer == other.Comparer || Comparer.Equals(other.Comparer)`)
therefore ensures only `Implies(Comparer == other.Comparer, Result)`. The copy
constructor and the set operations *require* the two comparers to be equal values, which
is what their fast path relies on (27.3). `Cell.Same` and `Cell.Equal` in
`test/sortedset/Exact.cs` verify the lowering.

### R27.48 `Pal.Unreachable()`

`Pal.Unreachable();` is a ghost statement: a proof obligation that control never reaches
it. It is emitted as Pulse's `unreachable ()`, whose argument is `squash False`, and the
statements after it in its block are not translated at all. Runtime behaviour is unchanged
(the call is `[Conditional]`), and a path that does reach the point fails verification, so
nothing the dropped statements do is assumed away. A block ending in it is treated like
one ending in a `throw` (R22.11): no epilogue follows, and R27.45's constructor rewriting
adds no `return this` after it.

The copy constructor uses it for its fallback branch, which enumerates an arbitrary
`IEnumerable<T>`: under its contract `HasEqualComparer` holds, the branch above returns,
and the fallback is dead. `ArgumentNullException.ThrowIfNull(p)` on an `[Exactly]`
parameter is nothing, as at a non-nullable class type (R23.2).

### R27.49 A borrowing struct of another object; `SetEquals`

R27.41's held struct may borrow an object other than `this`: its initialiser may be the
struct's constructor, or an instance method of the owner class returning the struct
(`x.GetEnumerator()`), applied to `this` or to a parameter of the owner class (an
`[Exactly]` parameter of it included, R27.46, or a local naming one). The local may be
declared in any block of the method, outside any loop, lambda, local function, `try` or
`switch` section (PALCS0710 otherwise).

* At the declaration, a peer held closed is converted to its heap form
  (`class_C__to_heap`) at fresh heap names, which `Pal.Heap<K>()` and the region
  predicates in the struct's specs then resolve to (`$heap_K$peer`, R27.44). Its members
  are called with the peer as their borrowed owner, and loops carry its heaps as they carry
  the receiver's (R27.41).
* Where the block that converted it ends (the method's tail, R5.5b), the plain invariant
  is given back (`class_C__of_heap`); the other arm of an `if` still holds the plain form.
* A ghost statement's naming bracket names an object held at its heaps at them, as they
  are now (`inv_heap … h…`), and binds the heap names to the witnesses.
* R24.14's sinking of a loop's return guard into an `if` no longer appends the statements
  after the `if` to a branch that already ends in a `return`.

`SetEquals` walks two enumerators in step. The library `Pulse.Lib.CSharp.SetCompare`
(`SpecSetCompare` in C#) defines `same_keys c s t` (equal lengths, and equal under `c`
position by position), its walk lemmas `same_keys_step` and `same_keys_whole`, and proves
`same_keys_members`: on two strictly sorted sequences, `same_keys` is equality of the sets
they hold under `c`. The enumerator exposes `SpecCurrentTree` and `SpecCurrentIn` for the
holder's invariant: the current node is in the region with the key just yielded at its
root.

### R27.50 Receivers kept at their model; `IntersectWith`

`IntersectWith` merges `this` with another set and only then rebuilds `this`. Until the
rebuild, every call on the receiver hands it back unchanged, and the proof needs that
fact at the merge loop's invariant. R27.50 keeps it in the following ways.

* **Reference equality with the receiver.** `other == this` (or `!=`), on two objects of
  one translated class, is R27.8's `ref_eq`. Other comparisons of two objects stay
  refused (R18.1, PALCS0593). Each such class gets a generated ghost `class_C__distinct`, proved
  from the two full `B.pts_to` it is handed. Where both are held whole, `distinct` makes
  the comparison false, so `other` and `this` can be open together. It adds no trusted
  item beyond `ref_eq`.
* **`as` that folds to null.** `D? x = e as D` is aliased to `null` when the frontend
  folds the test to `null`, and `null == null` folds to `true`.
* **Read-only calls do not dirty the receiver.** R27.16 assumes an unknown callee writes
  the region. The receiver test here skips callees that are read-only (`[Frac]`, or
  derived from the write set).
* **Pristine receivers.** A receiver is *pristine* where no statement before (on the
  emitted path) and, inside a loop, no statement of the loop body, can change it. The
  two arms of a tail `if` and a null window start from the state at the branch, since
  R22.12 copies the rest of the block into each arm. Where the receiver is pristine:
  * a call on it closes it at its pre-model (`fold inv_heap this pre h…`) rather than at
    the abstraction of its record;
  * a loop's invariant states `abs` at the pre-model, and its `decreases` reads
    `this`'s specs through that model;
  * a value-returning `if` (the `&&` of a condition) whose arm calls the receiver ends
    each arm with the receiver closed at that model. That is one term on both sides,
    and the receiver is reopened once after the join. Pulse's join keeps what one arm
    knows of a fresh record only under that arm's condition, and cannot abstract a
    heap that only pure facts still mention, so an arm that ends by reopening after a
    read-only callee drops that reopening instead of closing again. A callee taking the
    receiver without its heaps gives them back (`to_heap`) before it is reopened.
* **Read-only methods are heap-indexed.** A read-only method of a region owner is held
  at its heaps (R27.13), which it gives back as it found them. So a caller part-way
  through an enumeration keeps what it knew of them across `Max` or `Comparer`.

`IntersectWith` (with `other` `[Exactly]` a `SortedSet<T>` of the same comparer) is
proved with the library `Pulse.Lib.CSharp.SetInter` (`SpecSetInter` in C#).
`inter c s t` is the elements of `t` that compare equal to some element of `s`, in
`t`'s order. The library proves these lemmas:

| lemma | statement |
|---|---|
| `inter_step` | one merge step over strictly sorted suffixes |
| `inter_whole` | the whole sequences are their suffixes from 0 |
| `inter_finish` | when the merge has stopped, a prefix followed by the suffix intersection is the intersection, so the prefix is |
| `inter_sorted` | the intersection with a strictly sorted `t` is strictly sorted and no longer than `t` |
| `inter_left_empty` | nothing intersects an empty `s` |
| `push_prefix` | writing `x` at `k` extends the prefix `m[0..k)` by `x` |

`HasEqualComparer` is marked `[Frac("p")]`, which its write set already allows.

### R27.51 `foreach` over an owner; `Overlaps`

`Overlaps` enumerates another set with `foreach` and asks `this` about each element.
R27.51 translates that loop.

* **Lowering.** `foreach (T x in o)` where `o` is `this`, a parameter of the method's own
  class, or an `[Exactly]` parameter (R27.46), and `o`'s class has a translated
  `GetEnumerator` returning a borrowing struct `E` (R27.37), lowers to
  `E x__enumerator = o.GetEnumerator(); while (x__enumerator.MoveNext()) { T x = x__enumerator.Current; body }`.
  The enumerator is held as R27.41 holds a local, for the loop and nothing after it.
  The `foreach` must be a statement of a method's block, outside any loop, lambda,
  `try` or `switch`; anywhere else it is PALCS0714. A `foreach` over an array or a
  `List<T>` is unchanged.
* **Naming the enumerator.** `Pal.Enumerator<E>(x)`, in the loop's `Pal.Invariant` and
  `Pal.Decreases`, is the enumerator of the `foreach` that binds `x`. Only its `[Spec]`
  members may be read (`SpecReady`, `SpecPending`, …). The `MoveNext` contract then
  carries the invariant from one element to the next.
* **Interface properties of an `[Exactly]` object.** `c.Count`, where `c` is an
  `[Exactly]` parameter or a pattern variable bound to one (`other is ICollection<T> c`),
  is the exact class's implementation of the interface property.
* **A held local in a spliced block.** A loop whose rest of the block is copied into its
  exits (R22.12) splices that block flat, so a held local declared in it is closed in tail
  position as R27.41 requires.

`Overlaps` (with `other` `[Exactly]` a `SortedSet<T>` of the same comparer) is proved with
`Pulse.Lib.CSharp.SetOps` (`SpecSetOps` in C#). `overlaps c s t` holds when some element of
`t` is a member of `s` (`key_index c s x >= 0`). The library proves these lemmas:

| lemma | statement |
|---|---|
| `overlaps_step` | one step of the walk over the suffixes of `t` |
| `overlaps_whole` | the whole of `t` is its suffix from 0 |
| `overlaps_empty` | nothing overlaps an empty `s` (a pattern) |
| `overlaps_disjoint` | two strictly sorted sequences whose ranges are disjoint share no member; this justifies the `Min`/`Max` shortcut |

The loop calls `Contains` on the receiver, which R27.50 keeps at its model only when the
callee is read-only. `Contains` and `FindNode` call the comparer, an interface method that
the write-set scan counts as a write. So they are marked `[Frac("p")]`, which their write
sets allow.

### R27.52 A receiver changed by calls inside a loop; `ExceptWith`

`ExceptWith` enumerates another set with `foreach` and, for each element in range, calls
`Remove` on `this`. Between those calls it reads `this`'s fields (`comparer`). So the loop
holds the receiver open (R4.10), and every call closes and reopens it at a new model
(R22.15). R27.38 carries the receiver's model across a loop only when the loop leaves the
receiver unchanged. R27.52 covers a loop that changes it.

* **The model across the loop.** Take a class with regions, no `[Invariant]`, and no
  array or object fields. The class module defines `class_C__abs_rep r heaps`, which is
  every conjunct of `class_C__abs` except the model equation. It also defines
  `class_C__abs_model r heaps`, the model that the record and heaps abstract. A loop
  that reopens such a receiver and does not leave it unchanged carries:
  * an existential model `m` of the class's refined model type;
  * the resource `pure (m == class_C__abs_model r heaps)`, which tells Pulse what `m` is;
  * the conjunct `class_C__abs_rep r heaps`.

  `this` in the loop's `Pal.Invariant` then names `m`, the model at the current
  iteration, and not the model on entry.
* **Each arm meets the invariant.** A call in one arm of an `if` reopens the receiver at
  a record of its own. Pulse's join keeps what that arm knows of the record only under
  the arm's condition. It keeps nothing that relates the joined record to the record
  the other arm left untouched. So a loop body (with no `for` step) under this rule is
  emitted in tail position (R5.8d). Each arm, and each escape guard's arm (R5.10), is
  then checked against the invariant directly, and nothing is joined.

`ExceptWith` (with `other` `[Exactly]` a `SortedSet<T>` of the same comparer) ensures
`SpecItems == SpecSetOps.Except(c, old SpecItems, other.SpecItems)`. Here
`except c s t` removes the elements of `t` from `s` one at a time, in order, each by
`TopDownRemove.removed`, which is `Remove`'s own specification. The library proves:

| lemma | statement |
|---|---|
| `except_step`, `except_whole` | one more element of `t`; the whole of `t` is its prefix of full length |
| `except_skip` | an element outside the range of `s` removes nothing (the `continue`, and the element that triggers the `break`) |
| `except_break` | once an element is above `s`'s maximum, so is every later one, and nothing more is removed (the `break`) |
| `except_disjoint` | two strictly sorted sequences with disjoint ranges: nothing is removed (the shortcut when the ranges do not overlap) |
| `except_empty` | removing from an empty `s` leaves `s` (a pattern) |

### R27.53 Non-null owners; a conditional over calls that change the receiver; `SymmetricExceptWith`

* **A non-nullable owner is not null.** A reference at a non-nullable C# type of a
  translated class is an object of that class. Its translation has no null value. (A
  recursive class, R10.8, and a region's class, R27.3, are the exceptions: their
  pointers can be null.) So `x == null` on such a reference is `false`, and `x != null`
  is `true`. The typical use is `Debug.Assert(other != null)` on a `SortedSet<T>`
  parameter. Before this rule, the test was R10.7's window test, which a `Debug.Assert`
  cannot hold.
* **A conditional whose arms change the receiver.** Consider a loop body (in tail
  position, R5.8d) that declares `T x = c ? a : b;` where `a` or `b` calls a method that
  may change its receiver (R4.11). Emitted as `let x = if c { a } else { b }`, Pulse
  joins the two arms at a fresh model. It keeps the facts of only one arm, and only under
  that arm's condition (`SymmetricExceptWith`'s `Contains(item) ? Remove(item) :
  Add(item)` lost `Remove`'s postcondition this way). So the declaration becomes
  `if (c) { T x = a; rest } else { T x = b; rest }`. The rest of the body is copied into
  both arms, and each arm is checked against the loop invariant.

`SymmetricExceptWith` enumerates `other` (an `[Exactly]` `SortedSet<T>` of the same
comparer). For each element it calls `Remove` if the element is a member of `this`, and
`Add` otherwise. Its specification is `SpecSetOps.SymmetricExcept(c, old SpecItems,
other.SpecItems)`. Here `sym_except c s t` flips the membership of each element of `t`
in turn. A member is removed by `TopDownRemove.removed`, which is `Remove`'s
specification. A non-member is inserted by `TopDownHeap.inserted`, which is `Add`'s
specification. The library proves:

| lemma | statement |
|---|---|
| `sym_except_step`, `sym_except_whole` | one more element of `t`; the whole of `t` is its prefix of full length |
| `sym_except_length` | after `i` elements, the length is at most `s`'s length plus `i`. This is what keeps `Add`'s `count` from overflowing, under the requirement that the two lengths sum to at most `int.MaxValue` |

### R27.54 `do`-`while`; choosing between borrowing locals; a loop that breaks inside an arm

* **`do S while (c);`** is lowered to `while (true) { S; if (!c) break; }`. Its invariant
  and `Pal.Decreases` are the first statements of `S`, as for `while`. They are checked on
  entry, before `S` has run once, and after every iteration, including the one that breaks.
  So an invariant names the break with `Pal.Broke()` (R5.8), typically as
  `Pal.Implies(!Pal.Broke(), …)`. A `continue` aimed at the `do` loop is refused (it would
  skip the test).
* **`S x = c ? a : b;` over borrowing structs.** When `a` and `b` are held borrowing-struct
  locals (R28) that the rest of the method never names again, and `x` is never assigned, the
  copy is an alias. The rest of the block is lowered twice, under `if (c)`, with `x` standing
  for `a` in one arm and for `b` in the other. Every use of `x` is then a use of the original
  holder, which keeps its borrow and its owned state. The syntactic check that the originals
  are dead after the declaration is what makes the alias sound: no write through `x` can be
  observed through `a` or `b`.
* **A loop that breaks, inside an arm.** A non-tail `if` whose arm contains a loop with a
  `break` (whose flag is a `let mut`) cannot be joined by Pulse without an annotated
  postcondition. The emitter pushes the rest of the block into both arms, as for R27.53.
* **A loop-tail `if` without `else`** whose arm calls a method that may change its receiver
  is emitted as a tail with an empty `else`, so its facts are not lost at the join.

`test/sortedset/Walk.cs` (`CountRest`, `TouchSome`) exercises all four.

### R27.55 Adopting a local owner's tree; `UnionWith`

* **`this.f = d.g` where `d` is a local object of the same owner class** (R27.44) and `g`
  is its region field. The region of `d` is moved into the receiver's
  (`RegionMove.adopt`): `d`'s tree arrives unchanged and unshared, and every unshared tree
  already in the receiver's region is kept. `d` is then *open*: its later field reads are
  plain reads and its end of scope drops its bare fields. Its region is gone, so a method
  call on `d` after the adoption fails verification, which is sound. `UnionWith`'s
  empty-set branch (`root = dummy.root; count = dummy.count;` after a copy construction)
  is the use.
* **`UnionWith(other)`** (`other` `[Exactly]` a `SortedSet<T>` of the same comparer, and at
  most 2^30 elements together, for `ConstructRootFromSortedArray`) has three branches. An
  empty set copies `other`. When `other` is more than half this set's size, the two
  in-order enumerations are merged into an array (keeping `other`'s element on ties), and
  the tree is rebuilt from it. Otherwise each of `other`'s elements is `Add`ed
  (`AddAllElements`). `SpecSetOps.Union` is the merge and `SpecSetOps.AddAll` the
  repeated insertion; the library (`SetUnion`) proves the merge strictly sorted and its
  length at most the sum, and the loop lemmas the invariants use.
* **`SymmetricExceptWith(other)`** calls `UnionWith` on an empty set. Its specification is
  nevertheless `SpecSetOps.SymmetricExcept` throughout: flipping the elements of a strictly
  sorted `other` into the empty set inserts each at the end, and so gives `other`, which is
  also the union (`SetUnion.sym_except_union_empty`).

### R27.56 The comparer is not null

`Comparer<T>.Default` is not the null reference (a modeling axiom,
`Order.default_comparer_not_null`). Every constructor stores `comparer ?? Comparer<T>.Default`,
so the model refines `Result.Comparer != null`. `UnionWith` passes its own comparer to the
copy constructor, which requires `(comparer ?? Default) == collection.SpecComparer`. That
holds only because the comparer is not null.

### R27.57 Representation-sharing subclasses

A `sealed` class `S` deriving from a class `B` that is verified at its exact type (R27.1),
and declaring no instance field, `[Model]` or `[Invariant]` of its own, *shares `B`'s
representation*: its objects are `B` records under `B`'s invariant and `B`'s model. It is
translated as `B`'s type. Only one thing differs, which body a virtual call reaches, and
pal-csharp decides that statically. `TreeSet<T>` (`SortedDictionary`'s set, which throws
on a duplicate key) is the use.

* **Exact types are tracked instead of behavioural subtyping.** pal-csharp does not check
  overrides against the base's contracts. Each translated object of `S` is known to be an
  `S` everywhere it is used. A virtual call on an `S` receiver binds to `S`'s override, or
  to `B`'s member when `S` does not override it, and is checked against that member's own
  contract. This is sound because:
  * objects of `S` come only from translated `new S(…)`;
  * every conversion of an `S` value to another type (an upcast to `B`, an interface, or
    `object`; a cast, `as` or `is` on it; passing it where another type is expected) is
    refused with PALCS0715;
  * a constructor or method of `S` that lets `this` escape at another type is refused too.

  So static class = exact class at every use, as R27.1 already assumes of `B`. An override
  may therefore strengthen or change its contract freely: `TreeSet.AddIfNotPresent` throws
  where `SortedSet.AddIfNotPresent` returns `false`.
* **Replicas.** A member of `B` that `S` inherits, and whose body reaches an override of
  `S` (through `this`-calls, transitively), is translated a second time with `this` an
  `S`: `S_member`, verified against `B`'s contract at `S`. The call graph is closed from
  the root's callees, so a member is not part of its own replica set unless it is really
  recursive. A replica's `[Throws]` clauses are those of `B`'s member plus the ones marked
  `[Throws(…, At = typeof(S<>))]`, which apply only at `S`. `SortedSet.Add` declares that
  at `TreeSet<>` it throws `ArgumentException` when the item is present, and
  `TreeSet_Add` is verified with that clause.
* **Constructors.** A constructor of `S` with no initializer calls `B`'s parameterless
  constructor (C#'s implicit `: base()`). `base.M(…)` in `S` is `this.M` at `B`'s member.
* `(IComparer<T>?)null` is `null_comparer` (R26.7).

Test: `test/sortedset/Alias.cs`. A `CappedTally<T>` overrides a virtual `BumpCore` to
throw at a cap, and the inherited `Bump` is replicated with `[Throws(…, At = …)]`.
`test/diagnostics/cases/AliasUpcast.cs` is the refusal.

### R27.58 `SortedDictionary`: a holder of a region owner; `KeyValuePairComparer`

`SortedDictionary<TKey, TValue>` owns a `TreeSet<KeyValuePair<TKey, TValue>>` (R27.57)
through its field `_set`. Its model is `{ Pairs, PairComparer, KeyComparer }`, built from
`_set`'s `SpecItems` and `SpecComparer`, and refined so that `PairComparer` is
`SpecKeyMap.OfKeys(KeyComparer)`. `SpecKeys` is `SpecKeyMap.Keys(Pairs)`.

* **`KeyValuePairComparer`** is bound (`[SpecBinding]`, as in `pal/SortedSet/Bindings.cs`) to
  `KeyComparer.pair_comparer`, a comparer on pairs. Its constructor is bound to
  `KeyComparer.create c = of_keys (c ?? Default)`. `of_keys c` compares two pairs by their
  keys under `c`, and `key_of (of_keys c) == c`. These are trusted modeling axioms, listed
  in 27.1. `KeyMap` (proved) relates the pair set to its keys: under `of_keys c`, a
  strictly sorted pair sequence has strictly sorted keys, and
  `KeyIndex(of_keys c, ps, (k, v)) == KeyIndex(c, Keys(ps), k)` whatever `v` is. This is
  what turns `_set`'s pair contracts into `SortedDictionary`'s key contracts.
* **Binding a nested type** of a generic class applies the outer type arguments
  (`SortedDictionary<K, V>.KeyValuePairComparer` is `pair_comparer K V`). Type arguments
  that F* cannot infer are passed explicitly.
* **A call on an owned field whose contract holds the field at its heaps** (R27.13) is
  bracketed by `to_heap`/`of_heap` on the field, as on a local (`_set.Count`).
* **Sharing.** A class whose invariant owns, through an object field, a region owner is
  not fraction-shareable, because a region owner is not. Read-only members of such a
  class take the invariant at a fraction without splitting it.
* **Compound type arguments** in an applied type name are parenthesised
  (`class_SortedSet (tuple2 k v)`).

Test: `test/sortedset/Holder.cs`.

### R27.59 Reading a region pointer through an owned field

A method of a class that owns, through a field `f`, an object that owns region `K` reaches
`K` through `f`. It does not hold `K` itself (R27.16). A call on `f` whose contract holds
`f` at its heaps (R27.13) and returns a `K` pointer leaves `f` *open* at the heap the call
left it at: `class_O__inv_heap f m h` is unfolded, so the region is in the context at `h`,
and the facts the contract states of the result at `h` hold of it. The pointer is then read
through the region like any other (R27.5). The field is closed (`fold inv_heap`, then
`of_heap`) on every path that closes the receiver, and before the next call on `f`.
Writes through the pointer are not supported: the field is refolded at the model it was
opened at.

The rule for a `[Region]` class's auto-property (R27.3) now also matches it on a
constructed type (`TreeSet<KeyValuePair<K, V>>.Node.Item`).

Uses: `SortedDictionary.TryGetValue` and the indexer's getter read
`_set.FindNode(…)`'s node. Test: `test/sortedset/Holder.cs`.

### 27.1 Trusted assumptions

* `RefEq.ref_eq` (R27.8).
* `NullComparer.null_comparer` (R27.2).
* Exact-type verification (R27.1) is a soundness argument rather than an axiom. It holds as
  long as verified code obtains every `SortedSet` it holds from a translated constructor.
* Comparers are R22.30's total preorder.
* `Order.default_comparer_not_null` (R27.56): `Comparer<T>.Default` is not null.
* `ComparerIdentity.same` (R27.47): a comparer value stands for one object, so `==` on
  comparers is equality of values. `ComparerIdentity.equals` is a function of its
  arguments and nothing more.
* `KeyComparer` (R27.58): `of_keys c` compares pairs by their keys under `c`,
  `key_of (of_keys c) == c`, and `of_keys c` is not null. The runtime harness binds
  `SortedDictionary<K, V>.KeyValuePairComparer` and its constructor to this model.
* Exact types for representation-sharing subclasses (R27.57) are, like R27.1, a soundness
  argument that rests on PALCS0715's refusals rather than an axiom.
* The runtime harness binds `BitOperations.Log2(uint)` to `Arith.log2_u32`, the floor of
  the base-2 logarithm with `Log2(0) == 0`. It also binds
  `EnumerableHelpers.GetEmptyEnumerator<T>()` to R29.4's `Obj.empty_enumerator`.

### 27.2 What is verified in `SortedSet<T>`

The model is `SortedSetModel<T> { Tree: SpecTree<(T, bool)>; Comparer; Count }`. Each node
contributes `(Item, Color == Red)`.

**Verified.** Every ensures is stated over `SpecItems` (R27.11). Each read-only member also
ensures that the tree and the comparer are unchanged.

| member | ensures |
|---|---|
| `SortedSet()` | empty, comparer `Comparer<T>.Default` |
| `SortedSet(IComparer<T>?)` | empty, comparer `comparer ?? Comparer<T>.Default` |
| `SortedSet(IEnumerable<T> collection, IComparer<T>?)` (`collection` `[Exactly]` a `SortedSet<T>`, R27.46; requires `comparer ?? Comparer<T>.Default` to be `collection`'s comparer) | `SpecItems` and `SpecComparer` are `collection`'s, which is unchanged. The fallback branch is proved dead (R27.48) |
| `SortedSet(IEnumerable<T> collection)` (likewise, with `collection`'s comparer `Comparer<T>.Default`) | the same |
| `HasEqualComparer(other)` | `Implies(SpecComparer == other.SpecComparer, Result)` (R27.47); both sets unchanged |
| `Count`, `TotalCount` | `Result == SpecItems.Length` |
| `Comparer` | `Result == SpecComparer` |
| `IsWithinRange` | `Result` (the set has no range) |
| `Clear` | empty, comparer unchanged |
| `VersionCheck`, `UpdateVersion` | model unchanged |
| `FindNode` | `(Result != null) == (Pal.KeyIndex(SpecComparer, SpecItems, item) >= 0)`, and a found node is well-formed at the owner's heap with the found key at its root (R27.13) |
| `Contains` | `Result == (Pal.KeyIndex(SpecComparer, SpecItems, item) >= 0)` |
| `TryGetValue` | `Result == (KeyIndex >= 0)`, and then `actualValue` is `SpecItems[KeyIndex]` |
| `InternalIndexOf` | requires `SpecNodes.Height <= 30`; `Result == HeapIndex(SpecComparer, SpecNodes, item, 0)`, `(Result >= 0) == (KeyIndex >= 0)`, `Result <= Breadth(SpecNodes) - 2` (R27.14) |
| `FindRange` (both overloads) | `(Result != null) == AnyInRange(SpecComparer, SpecItems, from, to, …)`, and a result is well-formed with its root key in range |
| `MinInternal`, `Min` | `SpecItems[0]`, or `default(T)` when empty |
| `MaxInternal`, `Max` | `SpecItems[SpecItems.Length - 1]`, or `default(T)` when empty |
| `AddIfNotPresent`, `Add` (require `SpecItems.Length < int.MaxValue`) | `Result == (KeyIndex(Old(SpecComparer), Old(SpecItems), item) < 0)`; when added, `SpecItems == SpecTopDown.Inserted(…)` (inserted at its `LowerBound`); otherwise unchanged; comparer unchanged. The owner's invariants (sorted, red-black, `Count == Size`) are re-established (R27.26) |
| `InsertionBalance` (`[Open]`, R27.23) | `SpecTopDown.Balanced`: the rotation that repairs a red parent, re-linked under `greatGrandParent` or at the root; fields other than `root` unchanged |
| `ReplaceChildOrRoot` (`[Open]`) | `SpecTopDown.Replaced`: `parent`'s link, or `root` when `parent` is null, now `newChild` |
| `DoRemove`, `Remove` | `Result == (KeyIndex(Old(SpecComparer), Old(SpecItems), item) >= 0)`; `SpecItems == SpecTopDownRemove.Removed(…)` (the element at `KeyIndex` taken out, or unchanged); comparer unchanged. The owner's invariants are re-established (R27.30) |
| `ReplaceNode` (`[Open]`) | `SpecTopDownRemove.RnPost` under `RnPre` (R27.30) |
| `InOrderTreeWalk([Callback] action)` | `SpecWalk.Walked(SpecItems, Trace(action), Result)` (R27.39): `action` was called on the items in order and the walk stopped at the first `false` |
| `CopyTo(array, index, count)` | throws on a negative `index` or `count` or too short an array; otherwise `SpecWalk.CopyResult(SpecItems, Old(array), array, index, index + count)`: the first `min(count, Count)` items at `index`, the rest of the array unchanged |
| `CopyTo(array)`, `CopyTo(array, index)` | `array == Pal.Splice(Old(array), index, index + SpecItems.Length, SpecItems)` |
| `BreadthFirstTreeWalk([Callback] action)` | `SpecWalk.BfWalked(SpecItems, Trace(action), Result)` (R27.40): every call was on a member, all but the last returned true, and a true result means every member was called on |
| `RemoveWhere(match)` | `SpecItems == Pal.RemoveAll(Old(SpecItems), match)`, `Result == Old(SpecItems).Length - SpecItems.Length`, comparer unchanged (R27.40) |
| `SetEquals(other)` (`other` `[Exactly]` a `SortedSet<T>`; requires equal comparers) | `Result == SpecSetCompare.SameKeys(SpecComparer, SpecItems, other.SpecItems)`, which on the two strictly sorted sets is set equality (R27.49). The fallback branch is proved dead (R27.48) |
| `Overlaps(other)` (`other` `[Exactly]` a `SortedSet<T>`; requires equal comparers) | `Result == SpecSetOps.Overlaps(SpecComparer, SpecItems, other.SpecItems)`: some element of `other` is a member; both sets unchanged (R27.51) |
| `ExceptWith(other)` (`other` `[Exactly]` a `SortedSet<T>`; requires equal comparers) | `SpecItems == SpecSetOps.Except(c, old SpecItems, other.SpecItems)`: each element of `other` removed in turn, as `Remove` specifies; comparer and `other` unchanged (R27.52) |
| `IntersectWith(other)` (`other` `[Exactly]` a `SortedSet<T>`; requires equal comparers and at most 2^30 elements, for `ConstructRootFromSortedArray`) | `SpecItems == SpecSetInter.Inter(SpecComparer, Old(SpecItems), Old(other.SpecItems))`, the elements of `other` that compare equal to one of this set's; comparers and `other` unchanged (R27.50) |
| `SymmetricExceptWithSameComparer(SortedSet<T> other)` (requires equal comparers and the two sizes to sum to at most `int.MaxValue`) | `SpecItems == SpecSetOps.SymmetricExcept(c, Old(SpecItems), other.SpecItems)` (R27.53) |
| `AddAllElements(collection)` (`[Exactly]`; requires equal comparers and the sizes to sum to at most `int.MaxValue`) | `SpecItems == SpecSetOps.AddAll(c, Old(SpecItems), collection.SpecItems)`: each element `Add`ed in turn (R27.55) |
| `SymmetricExceptWith(other)` (`[Exactly]`; requires equal comparers and the sizes to sum to at most 2^30) | `SpecItems == SpecSetOps.SymmetricExcept(c, Old(SpecItems), other.SpecItems)`. An empty set goes through `UnionWith`, which gives the same set (`SetUnion.sym_except_union_empty`: both are `other`'s elements). The array fallback is proved dead |
| `UnionWith(other)` (`[Exactly]`; requires equal comparers and the sizes to sum to at most 2^30) | `SpecItems` is `SpecSetOps.Union(c, Old(SpecItems), other.SpecItems)` when the set was empty or `other` is more than half its size, and `SpecSetOps.AddAll(…)` otherwise (R27.55; see 27.3 for why the two differ) |
| `ConstructRootFromSortedArray` (static) | `Tree(Result) == Build(arr, startIndex, endIndex, Old(Tree(redNode)))`, unshared, re-linking `redNode`; with no `redNode`, red-black with keys `arr[startIndex..endIndex]` (R27.32) |

**`Enumerator` (R27.37, R27.38).** The struct borrows the set (`_tree`) and owns its
`Stack<Node>` (`_stack`). `Pending` is `SpecWalk.Pending(_reverse, heap, _stack.Items)`,
the keys the stack still owes, and `Walkable` says every stacked pointer is non-null and
well-formed.

| member | ensures |
|---|---|
| `GetEnumerator`, `Enumerator(set)` | borrows `set` at its version, forward, `Walkable`, `Pending == set.SpecItems` |
| `Enumerator(set, reverse)` | the same, with `Pending == Reverse(set.SpecItems)` when `reverse` |
| `Initialize` (requires an empty stack) | `Walkable`, `Pending == SpecWalk.Keys(_reverse, set.SpecNodes)` |
| `MoveNext` (requires `Walkable`, `Pending.Length <= Count`) | throws when the set's version moved; otherwise `Result == (Old(Pending).Length > 0)`, a true result leaves `_current` well-formed with `Old(Pending)[0]` at its root, and `Pending` is `Old(Pending)` without that key |
| `Current` | the key at `_current`'s root, when there is one |
| `IEnumerator.Current` | throws when `_current` is null; otherwise boxes `_current`'s key (R29) |
| `NotStartedOrEnded` | `Result == (_current == null)` |
| `Reset`, `IEnumerator.Reset` | throw when the version moved; otherwise `Pending` is the whole walk again |
| `Dispose` | nothing |

So, while the version is unchanged, `MoveNext` yields `SpecItems` in order (or in reverse)
one key at a time.

`SpecPending` and `SpecReady` (R27.41) name the pending keys and the state a holder keeps;
`SpecCurrentTree` and `SpecCurrentIn` (R27.49) the current node.

| member | ensures |
|---|---|
| `Reverse()` (R27.42) | `Pal.Yielded<T>() == Pal.Reverse(SpecItems)`; tree unchanged. Verified as one whole enumeration, holding `new Enumerator(this, reverse: true)` (R27.41) |

The runtime source keeps its expression-bodied `Comparer`, `Min` and `Max`. Their contracts
are on the properties.

**`Node` (R27.16).** Writers require `Pal.Unshared(@this)` and ensure `Pal.Unshared` of the
result and `Pal.Reshaped(@this, result)`, with the tree as below. `t` is
`Pal.Tree<(T, bool)>(@this)`.

| member | ensures |
|---|---|
| `IsRed`, `IsBlack`, `IsNonNullRed`, `IsNonNullBlack`, `IsNullOrBlack` | the root's colour (`SpecSearchTree.IsRed`) |
| `Is2Node`, `Is4Node` (requires `Pal.WellFormed`) | the colours of the root and both children |
| `ColorBlack`, `ColorRed` | `Recolor(t, …)` |
| `ShallowClone` | a fresh `t.RootOnly` (`Pal.Reshaped(null, Result)`) |
| `Split4Node`, `Merge2Nodes` | `Split4(t)`, `Merge2(t)`, under the 2-/4-node shape its `Debug.Assert`s check |
| `RotateLeft`, `RotateRight`, `RotateLeftRight`, `RotateRightLeft` | the rotation of `t` |
| `Rotate(rotation)` (requires `CanRotate`) | `Rotate(rotation, t)`, non-null |
| `GetSibling(node)` | the other child link (`Pal.LeftOf`/`Pal.RightOf`, R27.18) |
| `GetRotation(current, sibling)` | the rotation its two tests choose, and `CanRotate` of it |
| `Merge2Nodes` (removal) | also `SpecTopDownRemove.Merged`: every box where it was |
| `Rotate(rotation)` (removal) | also `SpecTopDownRemove.RotatedN`, the heap-level rotation |
| `Node(item, color)` | `Region.alloc` of a leaf (R27.16) |
| `ReplaceChild(child, newChild)` | `SpecTopDown.Relinked` |
| `DeepClone(count)` (requires unshared, `Size <= count`) | an unshared fresh tree equal to `t` (R27.43) |

The writers also ensure the heap-level prop `SpecTopDown` names for them (`Recolored`,
`Split4ed`, `Rotated`), which is what `AddIfNotPresent`'s ghost steps consume.

**`TreeSet<T>` (R27.57)**, the `sealed` subclass `SortedDictionary` uses, shares
`SortedSet<T>`'s representation.

| member | ensures |
|---|---|
| `TreeSet()`, `TreeSet(IComparer<T>?)` | as `SortedSet`'s constructors |
| `AddIfNotPresent` (override; requires `SpecItems.Length < int.MaxValue`) | `Result`, the item was absent, `SpecItems == SpecTopDown.Inserted(…)`, comparer unchanged; throws `ArgumentException` when the item is present |
| `Add` (replica `TreeSet_Add` of `SortedSet.Add`) | `SortedSet.Add`'s contract, plus its `[Throws(ArgumentException, …, At = typeof(TreeSet<>))]` |

**`SortedDictionary<TKey, TValue>` (R27.58, R27.59).** `KeyIndex` below is
`Pal.KeyIndex(SpecKeyComparer, SpecKeys, key)`. Every member throws
`ArgumentNullException` on a null key where the code checks it.

| member | ensures |
|---|---|
| `SortedDictionary()`, `SortedDictionary(IComparer<TKey>?)` | empty, key comparer `comparer ?? Comparer<TKey>.Default` |
| `Count` | `Result == SpecPairs.Length` |
| `Clear` | empty, key comparer unchanged |
| `ContainsKey` | `Result == (KeyIndex >= 0)` |
| `TryGetValue` | `Result == (KeyIndex >= 0)`, and then `value` is `SpecPairs[KeyIndex].Value`; pairs unchanged |
| indexer `get` | `SpecPairs[KeyIndex].Value`; throws `KeyNotFoundException` when `KeyIndex < 0` |
| `Add` (requires a non-null key that is absent, and `SpecPairs.Length < int.MaxValue`) | `SpecPairs == SpecTopDown.Inserted(SpecPairComparer, Old(SpecPairs), (key, value))`, key comparer unchanged |
| `Remove` | `Result == (Old KeyIndex >= 0)`, `SpecPairs == SpecTopDownRemove.Removed(…, (key, default))`, key comparer unchanged |
| `CopyTo(array, index)` (requires `index >= 0` and room) | `Contents(array) == Splice(Old(Contents(array)), index, index + SpecPairs.Length, SpecPairs)` |

`Add` and `CopyTo` *require* what makes them not throw, rather than stating `[Throws]`
(27.3: a holder's raise path).

**Not annotated:**

* **The rest of `SortedDictionary`.**
  * The indexer's `set` writes `node.Item` through a node of `_set`'s region (R27.59
    opens the field only for reading). Its model changes in a way that has to be proved
    to keep `_set`'s invariants: the key and so the order are unchanged.
  * `ContainsValue` passes capturing delegates to `_set.InOrderTreeWalk` that read nodes
    of `_set`'s region inside the delegate. It also needs a model of
    `EqualityComparer<TValue>.Default`.
  * `Comparer` casts `_set.Comparer` to `KeyValuePairComparer` and reads its field; the
    binding models the comparer, not its field.
  * `Keys`, `Values`, `KeyCollection` and `ValueCollection` keep a reference back to the
    dictionary in a lazily allocated object that the dictionary also points to.
  * `GetEnumerator` and `Enumerator` wrap `_set`'s enumerator, which borrows a field of
    the dictionary rather than the dictionary.
  * The `IDictionary<TKey, TValue>` constructors enumerate an arbitrary dictionary.
  * The non-generic `IDictionary` members cast `object` keys and values.
* **`TreeSubSet` and `GetViewBetween`.** Blocked on subclassing a region owner with state
  of its own. R27.57 covers a subclass that shares its base's representation, and
  `TreeSubSet` does not. A view is a `SortedSet<T>` subclass that inherits the fields and
  overrides the virtual members (`VersionCheck`, `Contains`, `IsWithinRange`,
  `MinInternal`, `AddIfNotPresent`, `DoRemove`, …). Four things are missing, each a
  general feature:
  1. **A subclass with its own invariant.** The view's `root` is a node *inside* the
     underlying set's region (`FindRange`'s result). Its subtree also holds keys outside
     the range, its `count` is recomputed lazily, and its `version` starts at -1. So none
     of the owner invariants (an unshared tree in its own region, `Count == Size`) holds of
     it. §9's hierarchy encoding gives each subclass its own model, but it covers abstract
     bases dispatched through a vtable. `SortedSet<T>` is concrete and verified at its exact
     type (R27.1), which is what lets its virtual calls bind statically.
  2. **Re-verifying inherited bodies at the subclass.** `base.Contains`,
     `InOrderTreeWalk`, `FindNode` and the enumerator run on a view receiver, with
     `VersionCheck` bound to the view's override. R27.57's replicas do this for a subclass
     with the base's invariant. A view's replicas would run on a different invariant, with
     the region borrowed from `_underlying` rather than owned. They would also need a
     library lemma: a search from `FindRange`'s node finds every in-range key.
  3. **A borrowing class that owns mutable fields.** The view borrows the underlying set
     (§28) and also writes its own `root`, `count` and `version` in `VersionCheck`. §28's
     borrowing classes have no such writable state.
  4. **Writing through a view.** `AddIfNotPresent`, `DoRemove` and `Clear` on a view
     modify the underlying set. A shared borrow cannot, and an exclusive one would forbid
     the underlying set's own use while the view is alive, which C# allows.

  The read-only uses in `IsSubsetOf` and `IsSupersetOf` (a view over the other set's
  `[Min, Max]` whose `Contains` is then called) need only 1–3.
* **The set operations other than `SetEquals`, `IntersectWith`, `Overlaps`, `ExceptWith`,
  `UnionWith` and `SymmetricExceptWith`.** `IsSubsetOf`, `IsSupersetOf` and their
  proper forms call `GetViewBetween` on their `SortedSet` branch, so they are blocked with
  `TreeSubSet`. Their other branches go through `CheckUniqueAndUnfoundElements`, the
  `BitHelper` path of 27.3's finding. The verified operations are verified only on their
  `SortedSet` branches (R27.50–R27.55).
* **`ICollection.CopyTo(Array, int)`.** It takes a non-generic `Array` and casts it to
  `T[]` or `object[]`, which pal-csharp does not model.
* **The copy constructor, beyond a `SortedSet` with the same comparer.** Both
  `SortedSet(IEnumerable<T>)` and `SortedSet(IEnumerable<T>, IComparer<T>?)` are verified
  for an argument that is exactly a `SortedSet<T>` whose comparer is the one the new set
  gets: `SpecItems` and `SpecComparer` are the argument's, which is unchanged. The
  features this took:
  * **A second object of the owner class.** Done (R27.44).
  * **Moving a tree between regions.** Done (R27.44).
  * **A body after `: this(comparer)`.** Done (R27.45).
  * **`collection as SortedSet<T>` on an interface parameter.** Done (R27.46):
    `[Exactly(typeof(SortedSet<>))]` specialises the constructor to callers whose argument
    is exactly a `SortedSet<T>`. Under it, `as` is the identity and
    `sortedSet is TreeSubSet` is false.
  * **The fallback branch.** It enumerates an arbitrary `IEnumerable<T>`
    (`EnumerableHelpers.ToArray`). It is dead when `HasEqualComparer` holds, which the
    contract ensures by requiring equal comparers (R27.47).

  The set operations (`SetEquals`, `IsSubsetOf`, …) and `TreeSubSet` meet the first and
  fourth of these as well. `TreeSubSet` is in addition a subclass that overrides the
  virtual members R27.1 verifies at the exact type.
* **The `IEnumerable<T>` constructor.** It sorts and deduplicates through `Array.Sort`
  and enumeration before it calls `ConstructRootFromSortedArray`, which is verified
  (R27.32).
* **Serialization.** This is out of scope.

### 27.3 Specification findings

* **`UnionWith` keeps a different representative depending on sizes.** When an element of
  `other` compares equal to one of this set's, the merge branch stores `other`'s element and
  the `Add` branch keeps this set's. With a comparer that identifies distinct values (for
  example case-insensitive strings), the result depends on the two sizes. The contract
  states the branch condition.

* **A holder cannot pass on a raise from an owned field.** When `SortedDictionary.Add`
  calls `_set.Add`, which may raise, the raise path leaves `_set`'s invariant at an
  unknown model. The callee's `raises` states only the throw condition, not that the
  comparer is unchanged. So the dictionary's invariant, refined by
  `PairComparer == OfKeys(KeyComparer)`, cannot be re-established for its own `raises`.
  Proving it would need a postcondition on the raise path. The verified contracts of
  `Add` and `CopyTo` therefore *require* what rules the throw out (an absent non-null key;
  a non-negative index with room). A caller relying on the `ArgumentException` for a
  duplicate key is outside the contract.
* **A `[Throws]` method cannot call a raising method while it owns a local object.** A
  callee's raise path leaves the caller's local objects behind, and the caller's raise
  clause has no way to drop them ("Leftover resources"). `RemoveWhere` would raise only on
  a null `match`, which R10 rules out, so it carries no `[Throws]`.
* **A pattern on `Seq.index` reaches every client.** A library lemma with
  `[SMTPat (Seq.index s j)]` fires on every indexing in every module that loads it. One in
  `SetFilter` made the unrelated `InOrderTreeWalk` time out. Its pattern is now the
  membership it is about.

* **`InternalIndexOf` and `BitHelper`.** `InternalIndexOf` returns a node's *breadth-first*
  index. The root is 0, and the children of `k` are `2k+1` and `2k+2`. That index is bounded
  by `2^height`, not by `Count`. `CheckUniqueAndUnfoundElements` sizes its `BitHelper` from
  `Count`, and `BitHelper.MarkBit` silently ignores an index past its capacity. So an
  element whose index falls outside is never marked, and a repeated occurrence of it is
  counted as unique again.

  Reproduced on .NET 10:
  * `new SortedSet<int>(0..39).SetEquals(xs)` returns `false` when `xs` lists every element
    twice.
  * `IsSubsetOf` is likewise wrong.
  * n = 4 and n = 10 happen to fit. n = 40, 100, 1000 and 100000 all fail.
  * Sequential inserts of 0..39 give indices up to 254, against 64 bits of capacity.

  Separately, `2 * index + 2` overflows `int` in a tree deeper than about 30 levels. A
  red-black tree reaches that depth only past about 2^15 nodes, but nothing bounds the
  arithmetic. The verified contract (R27.14) makes both facts explicit. `InternalIndexOf`
  *requires* `Height <= 30`, which is the precondition that rules out the overflow. Its
  result is bounded by `2^Height - 2`, not by `Count`.
* **Contracts on accessors were silently ignored.** An earlier version of this section
  moved `Count`, `Comparer`, `Min` and `Max` contracts onto `get` accessors. R9.20 never
  read them, so those members were "verified" against `true`. The `SortedList` sample had
  the same problem. R27.12 fixes the compiler. The runtime source keeps its original
  property syntax, with the attributes on the properties.
* **`greatGrandParent!` is not true.** `AddIfNotPresent` calls
  `InsertionBalance(current, ref parent!, grandParent!, greatGrandParent!)`, and
  `greatGrandParent` is `null` whenever the red parent is a child of the root. The callee
  handles it (`ReplaceChildOrRoot` takes a `Node?`), but its parameter is declared
  non-nullable. The verified source marks it `[AllowNull]` (R27.28).
* **More `!`s that are not true in `DoRemove` and `ReplaceNode`.** `DoRemove` calls
  `ReplaceNode(match, parentOfMatch!, parent!, grandParent!)`. `parentOfMatch` is `null`
  when the match is the root, and `grandParent`, the successor's parent, is `null` when the
  descent ends at the root's child. In `ReplaceNode`, `successor = match.Left!` is `null` when the match is a leaf, and
  `ReplaceChild`/`ReplaceChildOrRoot` are called with a `null` `newChild`. Each callee
  handles `null`. The verified source marks those parameters `[AllowNull]` (R27.28).
* **`ConstructRootFromSortedArray`'s midpoint overflows.** `(startIndex + endIndex) / 2`
  overflows `int` when the sum passes `int.MaxValue`, which needs an array longer than
  2^30 elements. The verified contract requires `arr.Length <= 2^30`. The usual
  `startIndex + (endIndex - startIndex) / 2` would not need the bound. The callers pass a
  deduplicated copy of their input, so such an array is possible in principle on 64-bit.
* **`++count` can overflow.** `AddIfNotPresent` increments `count` unchecked. The verified
  contract requires `SpecItems.Length < int.MaxValue`. A tree of 2^31 - 1 nodes is out of
  reach in practice, but nothing in the code rules it out.

* **An iterator's fail-fast is outside its contract.** `Reverse`'s body checks the version
  at every `MoveNext`. Its contract describes the enumeration with the set unchanged
  (R27.42), under which the check never fails. What a client that writes the set mid-way
  sees — an `InvalidOperationException` at the next step — is the dynamic check of R28.8,
  and is not stated.
* **`HasEqualComparer` trusts `IComparer<T>.Equals`.** The copy constructor and the set
  operations take `other`'s tree as sorted under `this.Comparer` when
  `Comparer == other.Comparer || Comparer.Equals(other.Comparer)`. If a user's comparer
  overrides `Equals` to return true for a comparer that orders differently, the
  constructor builds a set whose tree is not sorted under its own comparer, which breaks
  the owner invariant R27.11 states. A sound model needs `Equals` on comparers to imply the
  same order. That would be a trusted law, like R22.30's. The verified contracts do not assume
  it (R27.47): they require the two comparers to be one object (`==`), the only case in
  which the code's reliance on `Equals` is known to be right. A caller whose comparers
  differ but claim to be `Equals` is outside the contract, and gets a set whose tree may
  not be sorted under its own comparer.
  `Overlaps` relies on `Equals` too: it answers `false` without enumerating when the two
  ranges are disjoint under `this.Comparer`, which with a lying `Equals` can be wrong.
  Its contract therefore requires the same comparer as well (R27.51). So does
  `ExceptWith`'s, whose `Min`/`Max` shortcut and in-range `break` likewise read `other`'s
  order as `this.Comparer`'s (R27.52).

## 28. Enumerators: structs that borrow their collection

A collection's enumerator is a struct that refers to the collection without owning it:
```csharp
public struct Enumerator : IEnumerator<T>
{
    private readonly List<T> _list;      // borrowed
    private readonly int _version;       // the list's version when enumeration began
    private int _index;
    private T? _current;
}
```
The list may change between two `MoveNext` calls. When it does, `_version` no longer
matches and `MoveNext` throws `InvalidOperationException`. §28 translates such a struct
soundly, so that a contract can say what `MoveNext` does:
* when the versions agree, it steps through `Items`: it sets `Current` to `Items[i]` and
  returns `true`, or it returns `false` at the end;
* when they differ, it throws.

The harnesses are `pal/List`, `pal/Queue`, `pal/Stack`, `pal/HashSet`, `pal/PriorityQueue`
and `pal/SortedList` in the runtime checkout. `test/enumerators` pins the rules on smaller
code:
* `Bag.cs`: R28.1 to R28.5 and R28.4's loop facts;
* `Pairs.cs`: a struct nested in a class nested in a generic class, whose `Current` is a
  pair.

### R28.1 Borrowing structs

A struct is *borrowing* when:
* it is nested in a class `C` with a `[Model]` (directly, or through nested classes);
* it has exactly one instance field whose type is such an enclosing class;
* that field is `readonly`.

That field is the struct's *borrowing field*. Its value is a reference that the struct
does not own. The struct's other fields are its own state: plain values, a pair of them
(R26.10), or a type parameter.

### R28.2 A member is a method of the borrowed object's class

Each annotated member `M` of a borrowing struct `S` is translated as a read-only instance
method of `C`. The receiver is the borrowed object, shared at a fraction like any other
read-only receiver (§3). The struct is a second parameter:
```
fn func_S_M (ty…) (this: C) (self: S) …                       // reads only its fields
fn func_S_M (ty…) (this: C) (self: ref S) …                   // writes one of them
  requires inv this ** pure (self.borrowing_field == this) …
```

Two further requirements:
* the method requires that the borrowing field holds the receiver, and when it writes
  the struct it also ensures this;
* the method is generic in the type parameters of every enclosing type. These are
  gathered through enclosing classes as well as structs, so
  `PriorityQueue<E,P>.UnorderedItemsCollection.Enumerator` is generic in `E` and `P`.

Inside the member:
* `_list`, or a local bound to it and never written (`List<T> list = _list;`), is the
  receiver;
* the receiver's fields (`_list._items`, `_list._size`) are read under its invariant, as
  in any method of `C`;
* a call on it (`_list.Count`) is a call of `C`'s method on the receiver;
* the struct's own fields are read and written through `self`;
* a ref local of an array of the receiver (`ref Entry e = ref _hashSet._entries![_index++]`)
  is a read of that array.

A ghost statement in the body may name the receiver's fields as well. Its contract names
the receiver's spec members.

Getters and `void IEnumerator.Reset()` are named as R22 names them. The explicit interface
name is shortened to `Reset`.

### R28.3 Contracts name the struct's state and the reference

A contract of a borrowing member, or of a member of `C` that returns `S`, names the
struct's private fields (`@this._index`, `Result._version`). It also names the borrowed
object's spec members (`@this._list.Items`, `@this._list.SpecVersion`).

`ReferenceEquals(a, b)` in a contract is identity of two references. Each side must be one
of:
* a parameter of class type, including `@this`, which is the Pulse binder of the
  reference;
* a borrowing field.

Anything else is refused (PALCS0733). This is how `GetEnumerator` says which collection
the enumerator walks:
```csharp
[Ensures("ReferenceEquals(Result._list, @this) && Result._version == @this.SpecVersion && Result._index == 0")]
public Enumerator GetEnumerator() => new Enumerator(this);
```

### R28.4 Construction, and what a member keeps

The constructor `S(C owner, …)` is a function of `C`. The receiver is the parameter that
the constructor assigns to the borrowing field. The function returns the struct, and it
ensures that the struct's borrowing field holds the receiver. `new S(this)` inside `C` is a
call of that function on `this`. A borrowing struct is created only that way: an object
initializer is refused, and so is a constructor that does not take the object it borrows
(PALCS0730).

A member that writes the struct also ensures that it leaves each `readonly` value field
unchanged (`_version`). A caller therefore keeps `_version == list.SpecVersion` across
`MoveNext` calls.

A loop inside a member sees only its invariant. So a member that contains a loop takes a
snapshot of each `readonly` value field on entry, and every loop invariant implicitly
includes:
* the borrowing field still holds the receiver;
* each `readonly` field still equals its snapshot.

`HashSet<T>.Enumerator.MoveNext` is the case: it skips free slots.

### R28.5 The constructor's body

The constructor is translated as the value it builds. Its body assigns each field at most
once, and does nothing else. Each right-hand side may read the parameters and the borrowed
object, but not another field of the struct (PALCS0732). A field that the constructor does
not assign takes its type's `default`; for a type parameter, that is the caller's default
(R14.2a). A constructor that chains to another is refused (PALCS0730).

### R28.6 Calls

No verified code calls a member of a borrowing struct. `foreach` is not translated, and a
caller would also have to pass the borrowed object, which is not designed. Such a call is
refused (PALCS0731). The members are verified, and their contracts are the specification
that a `foreach` translation would use. (R27.41 admits one case: an owner's method holding
`new S(this, …)` in a local.)

### R28.7 The borrowed object is not written

A borrowing member writes only the struct's own fields, by assignment, `++` or `--`.
Writing a field of any other object is refused (PALCS0734). The null-forgiving `x!` is not
a write.

### R28.8 Versions

Each collection's model gains `Version`, which is `_version` (and `version` in
`SortedList`), and a spec member `SpecVersion`. The counter stays `[Wrapping]`. Nothing
else about the existing specifications changed: mutators still say nothing about
`SpecVersion`.

As a result, after a mutation an enumerator's `_version == SpecVersion` is unknown, so a
caller cannot prove that `MoveNext` will not throw. This is the specification that the BCL
promises, because it calls fail-fast "best effort". Because the counter wraps, 2^32
mutations bring the version back to its old value. The enumerator then continues over the
new contents without throwing, so fail-fast is not a guarantee. The contracts here do not
claim that it is.

### R28.9 Contracts on a getter

`[Ensures]` and the other contract attributes may be placed on a property's `get`
accessor instead of on the property:
```csharp
public int Count
{
    [Ensures("Result == @this.SpecCount")]
    get => _size;
}
```
Previously such contracts were silently dropped. When neither the property nor the getter
carries a contract, the member is not annotated, as before.

### What was verified

The harnesses verify 34 members:

| Collection | Verified |
|---|---|
| `List<T>` | `GetEnumerator`, and the enumerator's constructor, `MoveNext`, `Current`, `Reset` and `Dispose` |
| `Queue<T>` | the same six |
| `Stack<T>` | the same six, and `ThrowInvalidVersion` |
| `HashSet<T>` | the same six |
| `PriorityQueue<E,P>.UnorderedItemsCollection.Enumerator` | the constructor, `MoveNext`, `Current`, `Reset` and `Dispose` |
| `SortedList<K,V>.Enumerator` (private) | the constructor, `MoveNext`, `Reset` and `Dispose` |

`MoveNext`'s contract has this shape (List):
```csharp
[Throws(typeof(InvalidOperationException), "@this._version != @this._list.SpecVersion")]
[Ensures("@this._version == @this._list.SpecVersion")]
[Ensures("Result == (0 <= Old(@this._index) && Old(@this._index) < @this._list.SpecCount)")]
[Ensures("Implies(Result, @this._index == Old(@this._index) + 1 && Same(@this._current, @this._list.Items[Old(@this._index)]))")]
[Ensures("Implies(!Result, @this._index == -1)")]
```

The other collections differ in these ways:
* **Stack** enumerates from the top. `_index` starts at `Count` and counts down, and
  `MoveNext` sets `Current` to `Items[_index]` after the step. `-1` means finished.
* **Queue**'s cursor `_i` starts at `-1`, and `-2` means finished.
* **SortedList**'s `_index` runs from `0` to `Count + 1`. `MoveNext` sets `_key` and
  `_value` from `SpecKeys` and `SpecValues`.
* **HashSet** steps over free slots. Its model gains:
  * `Slots`, which is `_count`;
  * `Prefixes`, the sequence whose element `i` is the live items among the first `i`
    slots (`HashSetChain.prefixes`, proved).

  `MoveNext` ensures that on `true` it moved from `Old(_index)` to `_index`, and that
  `Prefixes[_index]` is `Prefixes[Old(_index)]` followed by `_current`. On `false` there
  were no more items. The lemma `HashSetChain.items_step` is proved.

§29 extends this to `KeyValuePair`, to classes that borrow, and to their caches; what is
still not annotated, and why, is listed at the end of §29.

### Findings

* `Stack<T>.Enumerator.MoveNext` checks the step against `_stack._array.Length`, not
  `Count`. That is correct only because the version check has already passed, which a
  `Debug.Assert` records. The contract requires `-1 <= _index <= SpecCount`. To be proved, `ThrowInvalidVersion` needed
  `[DoesNotReturn]` (the only change beyond pal attributes and ghost code).
* `SortedList`'s enumerator sets `_index = Count + 1` at the end. At `Count ==
  int.MaxValue` that would overflow, so `MoveNext` requires `SpecCount < int.MaxValue`
  (unreachable in practice).
* `Queue<T>.Enumerator` computes `_q._head + _i`, which overflows when `head + Count`
  exceeds `int.MaxValue`; it can when the capacity is above 2^30. `MoveNext` requires
  `SpecHead + SpecCount <= int.MaxValue` and `_i < int.MaxValue`.
* Fail-fast is incomplete because the version counter wraps (R28.8).

### Trusted

Nothing new. The proofs rely on the `ThrowHelper` stubs in `pal/common`, as every harness
does. There is no `admit` or `assume`.

## 29. Completing the enumerators: pairs, borrowing classes, caches

§28 left out the members that need a `KeyValuePair`, the views that are classes rather
than structs, and the caches that hold those views. §29 adds them. `test/enumerators/Pairs.cs`
pins each rule; the runtime harnesses are those of §28.

### R29.1 `KeyValuePair<K,V>` is a pair

`KeyValuePair<K,V>` is a value type with two fields and no behaviour, so it is translated
as the pair R26.10 gives a value tuple: F*'s `tuple2 K V`. The two are the same type in
the model, which is sound because no verified code can tell them apart: neither has
identity, and both compare only through their components.

| C# | F* |
|---|---|
| `new KeyValuePair<K,V>(k, v)`, `KeyValuePair.Create(k, v)` | `Mktuple2 k v` |
| `p.Key`, `p.Value` | `fst p`, `snd p` |
| `default(KeyValuePair<K,V>)` | the pair of the components' defaults (R14.2a) |

`SortedList<K,V>.Enumerator.Current` builds one, and its contract is
`Same(Result.Key, @this._key) && Same(Result.Value, @this._value)`.

### R29.3 Classes that borrow

A class is *borrowing* when it satisfies R28.1, with *class* for *struct*, and also:
* it is `sealed` and derives directly from `object`;
* it has no `[Model]` and is not `[Plain]`.

`SortedList.KeyList`, `ValueList`, `SortedListKeyEnumerator`, `SortedListValueEnumerator`
and `PriorityQueue.UnorderedItemsCollection` are borrowing classes.

Such a class is translated exactly as a borrowing struct: it is the record of its fields,
its members are methods of the owner's class taking the record as `self` (R28.2), and its
constructor returns the record (R28.4, R28.5). The object's identity is dropped. That is
sound because verified code cannot observe it:
* it cannot call the class's members (R28.6, PALCS0731), so it never holds a reference
  to one from which to observe sharing;
* it cannot compare references to one: `ReferenceEquals` accepts only class-typed
  parameters and borrowing fields (R28.3), and the class is neither;
* a member writes only the class's own fields (R28.7), and the class is `sealed`, so no
  override can do otherwise.

A member that writes the object's fields (`MoveNext`) takes `self` by reference, as for a
struct. Within one call, therefore, the record stands for the object's state, owned for
the call.

A property's `set` accessor is a member too. `KeyList`'s indexer setter is the method
`set_Item`, which throws `NotSupportedException`; its contract is `[Throws(…)]
[Ensures("false")]`. A constructor with an expression body (`=> _queue = queue`) is read
as its single assignment.

### R29.3b A view cache is outside the representation

An owner often caches its view:
```csharp
private KeyList GetKeyListHelper() => keyList ??= new KeyList(this);
public UnorderedItemsCollection UnorderedItems => field ??= new UnorderedItemsCollection(this);
```
A field whose type is a borrowing class is never part of a class's representation. Its
record names the owner, so including it would make the owner's type depend on itself.
Reading or writing such a field is refused (as R25.3 refuses an unmapped field), with
one exception, a *fill*. `f ??= new V(this)` is a fill when:
* `f` is an instance field (or a `field` backing field) whose type is a borrowing class
  `V`;
* `V`'s owner is the class declaring `f`;
* the right-hand side is exactly `new V(this)`;
* every write to `f` in its class is a fill of that form.

A fill is translated as `new V(this)`, and it does not count as a write in R4.11's
analysis, so the getter is read-only. This is sound for the following reasons:
* By the last condition, `f` only ever holds `null` or a `V` built from `this`.
* As a record (R29.3), that `V` is equal to the one `new V(this)` builds. Both
  branches of the `??=` therefore yield the same value.
* The write it performs changes nothing the model or the representation contains.

A `??=` on such a field that is not a fill is refused (PALCS0735).

A getter written with C#'s `field` keyword has a backing field, so R9.20 does not
collect it as a computed property. When the backing field's type is a borrowing class, it
is collected.

### R29.4 `object` is an opaque box

`object`, `IEnumerator`, `IEnumerator<T>` and `IDictionaryEnumerator` are translated as
`Pulse.Lib.CSharp.Obj.obj`, an abstract type. Every implicit conversion of a translated
value to one of them becomes `box v` (`val box (#a:Type0) (x:a) : obj`). Nothing is
assumed of `box`: in particular it is not injective, because two boxes of equal values
are distinct objects. A contract relates a result to what it boxes with
`Pal.Boxes(o, v)`, which is `o == box v`.

This is sound because verified code can do nothing with an `obj` but pass it on and
return it. Everything that would observe it is refused (PALCS0737):
* `==`, `!=` and `??` on an `obj`, and the `null` literal at type `obj`;
* `is`, `as`, `is` patterns, `?.`, and casts from `object` (unboxing);
* reading a field of type `obj` (such a field is not mapped: R25.3).

`Pal.Boxes(Result, e)` therefore pins down which value was boxed, and nothing can
contradict it. An `obj` result says nothing about the object's identity, which the model
does not have.

`DictionaryEntry` is a pair of boxes (`tuple2 obj obj`), as `KeyValuePair` is a pair (R29.1).

**Explicit interface members.** A member implementing an interface explicitly
(`object IEnumerator.Current`, `IEnumerator<T> IEnumerable<T>.GetEnumerator()`) is
translated when annotated. It is named by its short name; if another member of the type
has the same short name, by the interface and then the name (`IEnumerator_Current`,
`IEnumerable1_GetEnumerator`, `IDictionary_GetEnumerator`). Before R29.4 such a member was
silently dropped even when annotated.

**Self-calls in a borrowing type.** A member of a borrowing struct or class may call
another *read-only* member of the same type on `this` (`object IEnumerator.Current =>
Current`). The call passes the borrowed object and `self` on; the callee holds the owner
at the caller's fraction. A call to a member that writes the struct's fields is still
refused (PALCS0731). In a `sealed` borrowing type, `((I)this).M()` is the call of the
type's own implementation of `I.M` (Roslyn's `FindImplementationForInterfaceMember`): no
subclass can re-implement `I`.

**The shared empty enumerators.** `SZGenericArrayEnumerator<T>.Empty` and
`EnumerableHelpers.GetEmptyEnumerator<T>()` are bound (`SpecBinding`, in the harnesses)
to `Pulse.Lib.CSharp.Obj.empty_enumerator T : obj`, an uninterpreted object. This is a
modelling axiom: it asserts only that the read or call has no effect and does not throw,
which holds of a static readonly singleton and of `((IEnumerable<T>)[]).GetEnumerator()`.

A conversion is boxed exactly once. Roslyn reports the converted type `object` on a
parenthesised operand and on the operand of `!` as well as on the expression around it,
and on the operands of the predefined reference `==`; those are not boxed.

### R29.5 An array operand is named after the calls that follow it

In `Array.Copy(_dict.keys, 0, array, arrayIndex, _dict.Count)` the operands are evaluated
in order:
1. The emitter reads `_dict`'s record to name `keys`.
2. The call `_dict.Count` refolds `_dict`'s invariant.
3. The next unfold names a fresh record.

The array's permission is then stated about a record that Pulse cannot relate to the
first one.

The fix applies to an array primitive (`Array.Copy`, `IndexOf`, `BinarySearch`, …). An
array-field operand of such a primitive is read again after the last operand when:
* every call among the later operands is a read-only instance call (R4.11b), which holds
  its receiver at an arbitrary fraction and so cannot write the object;
* no such call passes a reference or an array;
* nothing among the later operands runs statements.

Under those conditions the re-read yields the value C# read. Otherwise the operands are
left as they were, and the result is at worst a proof failure, never an unsound
translation.

### What §29 verifies

With §28, the six harnesses verify 101 enumerator and view members:

| Collection | Verified |
|---|---|
| `List<T>`, `HashSet<T>`, `Queue<T>` | §28's six, `IEnumerator.Current`, `IEnumerable<T>.GetEnumerator` (8 each) |
| `Stack<T>` | the same, and `ThrowInvalidVersion` (9) |
| `PriorityQueue.UnorderedItemsCollection` | the constructor, `Count`, `GetEnumerator`, `IEnumerable<…>.GetEnumerator`, `IEnumerable.GetEnumerator`; its enumerator's constructor, `MoveNext`, `Current`, `IEnumerator.Current`, `Reset`, `Dispose`; the owner's `UnorderedItems` (12) |
| `SortedList<K,V>.Enumerator` | the constructor, `MoveNext`, `Current` (a `KeyValuePair`), `IEnumerator.Current`, `IDictionaryEnumerator.Key`, `.Value`, `.Entry`, `Reset`, `Dispose` (9) |
| `SortedList<K,V>` | `GetEnumerator`, `IDictionary.GetEnumerator`, `IEnumerable<…>.GetEnumerator`, `GetKeyListHelper`, `GetValueListHelper` (5) |
| `SortedListKeyEnumerator`, `SortedListValueEnumerator` | the constructor, `MoveNext`, `Current`, `IEnumerator.Current`, `Reset`, `Dispose` (6 each) |
| `KeyList`, `ValueList` | the constructor, `Count`, `IsReadOnly`, the indexer's `get` and `set`, `Add`, `Insert`, `Clear`, `Remove`, `RemoveAt` (the mutators throw `NotSupportedException`), `Contains`, `IndexOf`, `CopyTo`, `GetEnumerator`, `IEnumerable.GetEnumerator` (15 each) |

`SortedList.GetEnumerator` is declared to return `IEnumerator<KeyValuePair<K,V>>`; its
contract states which enumerator it boxes. The concrete construction `new Enumerator(this,
KeyValuePair)` is translated as written; no translation at the dynamic type was needed.

### Not annotated, and why

* `IEnumerable.GetEnumerator() => ((IEnumerable<T>)this).GetEnumerator()` in `List`,
  `HashSet`, `Queue`, `Stack` and `SortedList`. The classes are not sealed: a derived
  class may re-implement `IEnumerable<T>`, so the call is an interface dispatch whose
  target is not known. (The same member of the sealed `UnorderedItemsCollection` is verified.)
* `SortedList.Keys`, `Values` and their explicit `IDictionary`/`IReadOnlyDictionary`
  forms. They return `IList<T>`, `ICollection<T>`, `IEnumerable<T>` or `ICollection`;
  `IList<T>` is translated as an array elsewhere, so a view converted to it has no
  translation. Their bodies are `GetKeyListHelper()`/`GetValueListHelper()`, which are verified.
* `ICollection.CopyTo(Array, int)`, `ICollection.SyncRoot`, `ICollection.IsSynchronized`
  on the views and the owners: an untyped `Array` and the owner as an `object` (the
  views' `SyncRoot` casts the owner to `ICollection`).

### Findings (§29)

* An annotated set accessor (`KeyList`'s indexer `set`) was silently dropped, and so
  were annotated explicit interface members. Both are translated now.
* A constructor with an expression body crashed the borrowing-constructor analysis.
* The operand order of R29.5: a call among later operands refolded the owner, and the
  array's permission was stated about a stale record.
* Boxing: Roslyn reports `object` as the converted type at several nested positions
  (parentheses, `!`, reference `==`), which first produced double boxes.
* `SortedList`'s `IEnumerator.Current` and `IDictionaryEnumerator` members compare
  `_index` with `Count + 1`, which overflows at `Count == int.MaxValue`; they require
  `SpecCount < int.MaxValue`, like `MoveNext` (§28).

### Trusted (§29)

`Pulse.Lib.CSharp.Obj` is implemented (`obj = unit`), so its interface carries no
assumption. The bindings of the two shared empty enumerators to `empty_enumerator` are the
only new trust: each says the read or call is pure and does not throw.

## 31. `LinkedList<T>`: rings of region nodes

`LinkedList<T>` keeps its nodes in a circular doubly-linked list: `head` is the first
node, each node's `next` and `prev` link it to its neighbours (the last node's `next` is
`head`), and every node points back to its list through `list`. §27's regions own
`SortedSet<T>`'s nodes as trees; a ring is not a tree, so §31 lets a region's nodes form
rings and states their shape through a library of pure functions and lemmas.

The harness is `pal/LinkedList` in the runtime checkout. `test/linkedlist/Chain.cs` pins
the rules on a smaller ring: R31.1 to R31.7 through insertion at the front and the back,
R31.8 to R31.10 through unlinking a node, R31.11 and R31.12 through `Link.Next` and
`Clear`, and R31.13 and R31.14 through `Fresh` and `Guard`.

### R31.1 Cyclic regions

`[Region(Cyclic = true)]` marks a region class whose two self-typed fields are the `next`
and `previous` links of rings. For such a class:
* the owner's invariant does not require its pointers to be unshared trees;
* a read of a node's field requires only that the node is in the region
  (`Pal.InRegion(x)`);
* the tree intrinsics `Pal.Tree`, `Pal.WellFormed`, `Pal.Unshared` and `Pal.Reshaped` are
  refused with PALCS0780.

The shape is the user's to state, through `SpecRing` (R31.4).

### R31.2 The cycle group

A ring's owner (a class with a field of a cyclic region class) and its nodes refer to each
other: `LinkedList<T>.head` is a node and `LinkedListNode<T>.list` is a list. The owner's
record is therefore declared in the region class's module, next to the node's, and the
owner's own module includes it from there. The owner is not recursive, so it has no
`intro_nil` (§10); its type arguments are written out where nothing else names them.

### R31.3 `@this` in an invariant

An owner's `[Invariant]` may name `@this`, the reference itself. The ring's invariant
says that the nodes the region owns are exactly those that point back to the owner:
```csharp
[Invariant("SpecRing.Ring<LinkedListNode<T>, LinkedList<T>>(Pal.Heap<LinkedListNode<T>>(), head, count, @this)")]
```

### R31.4 `SpecRing` and `Pulse.Lib.CSharp.RegionRing`

`SpecRing`'s members are `[RegionOp]`s or `[SpecOp]`s (R27.22) over
`Pulse.Lib.CSharp.RegionRing`. The region class's view is a pair of its item and its
owner. Each `void` member is a lemma, called as a ghost statement.

* Shape:
  * `Ring(h, hd, n, o)`: the ring of `n` nodes from `hd`, owned by `o`;
  * `Shape(h, hd, n)`: the same ring, whoever owns it;
  * `Nodes(h, hd, n)`, `Items(h, s)`, `Item(h, x)`, `Owner(h, x)`;
  * `Succ(h, hd, x)` and `Pred(h, hd, x)`, a node's neighbours as `Next` and `Previous`
    return them (null past either end), and `SuccAt`.
* Sequences: `Pos`, `InsIndex`, `InsertAt`, `RemoveAt`.
* Heap relations: `ViewsKept`, `Detached`, `Cleared` (every node of a prefix of a
  sequence is detached, and nothing else changed).
* Lemmas:
  * `Allocated`, `InsHead`, `Single`, `Rotated` and `Adopted` for insertion;
  * `Member`, `Owns`, `Neighbours`, `Ends` and `Removed` for reading and removing;
  * `At` for the node at a position;
  * `ClearStart`, `ClearNext`, `ClearStep` and `ClearDone` for `Clear`'s loop;
  * `Reowned` (writing a node's owner keeps the ring's shape) and `Reattached` (a node
    inserted and then pointed at the owner leaves the ring owned by it) for the
    overloads that insert a given node.
* Searches:
  * `IndexOf` and `LastIndexOf` are the first and last positions whose item *matches* a
    value: for a null value, the null items; otherwise the items that `EqualityComparer<T>.Default`
    says are equal;
  * `IndexFrom` and `LastFrom` are the same searches from or up to a position;
  * `FindStep` and `LastStep` are their one-step lemmas, for a loop's invariant.

Nothing in `RegionRing` is trusted beyond `Pulse.Lib.CSharp.RefEq.ref_eq` (R27.8).

### R31.5 The receiver as a region operation's argument

In a method body, `this` is the receiver's model (R4.2). A region operation's argument
`this` is the reference instead: the owner that the ring's nodes point back to.

### R31.6 `x?.F` as a value

`x?.F` on a region pointer, used as a value, is `x != null ? x.F : null`. This is R27.29's
statement form, as an expression. An `x` with an effect would be evaluated twice, and is
refused.

### R31.7 The model's refinement

`LinkedList<T>`'s model refines `Count >= 0 && Nodes.Length == Count && Items.Length ==
Count`. `RegionRing`'s `items_length` and `empty_ring` lemmas discharge it automatically
(through SMT patterns).

### R31.8 `x == this` with a nullable `x`

R27.50 compares `x == this` of an owner class by reference. `x` may now be nullable (a
node's `list`): a null box is unequal to `this`.

### R31.9 Clearing a node

`Invalidate` sets `list = null; next = null; prev = null;`.
* The `null` of a non-recursive class (the owner) is the typed null box, since such a class
  has no `intro_nil`.
* A write to a field of the receiver, named without `this.`, writes the region of the
  member's own class: it is in the method's write set.
* A region class's back pointer to its owner is not how a member reaches the region it
  lives in, so R27.59 does not apply to it.

### R31.10 A write of a ring's entry pointer splits the join

`if (head == node) head = node.next;` is not in tail position. A join would forget which
node `head` now is, and the `Removed` lemma after it needs that. An arm that writes a field
whose type is a cyclic region class is therefore treated like one that moves a region
(R27.16): the continuation is duplicated into both arms.

### R31.11 A node member that reads its owner

`LinkedListNode<T>.Next` is `next == null || next == list!.head ? null : next`: it reads
`head`, a field of the list its back pointer names. The node's region does not hold the
list. A member of a cyclic region class whose body reads `f.g`, where `f` is a field of the
node whose class owns the node's region (`list`, of type `LinkedList<T>`), is therefore
given the owner as an extra argument:

* an erased binder `owner_this` for the owner's box, and a fraction
  `B.pts_to owner_this #p rep` of its representation, which the member gives back;
* the precondition `owner_at view heap this == owner_this`: the node points back to it.

The read `list!.head` becomes `Region.read_owner owner_this t.list`, which reads the box at
the permission held once the pointer is known to be the owner. In a contract,
`@this.list!.head` is the field of `rep` (the frontend admits a field of the back pointer's
class there, and nowhere else outside the class).

The owner's binder is typed `B.box raw` and not the class's alias, so that an `if` whose
arms instantiate the box type differently still joins on one `pts_to`.

A call is admitted only from an instance method of the owner's class, with the receiver
open: the receiver's box is passed (`hide this`), and the precondition is then the fact
that the node's owner is the receiver, which `SpecRing.ClearNext` or `Owns` supplies.
Elsewhere the call is PALCS0781: no other caller holds the owner's representation.

### R31.12 A reference tested against null in a boolean

`current == null ? count : Pos(s, current)` puts a reference comparison in a conditional's
guard, which is a `bool`. A box has no decidable equality, so `=` does not typecheck; the
comparison with `null` is `B.is_null x` (or its negation).

### R31.13 A back pointer tested against null in code

`node.list != null` reads a field of a region node whose type is a class that is not a
region class (the owner). In code, the comparison is `B.is_null` of the field read,
bound by its own `let` so that the solver sees `is_null`'s refinement; R31.12 is the same
test in a contract. In a contract, R27.53 folds `x != null` to `true` for an `x` that is
never null; a spec method whose result is `O?` (such as `SpecRing.Owner`) may return null,
and is no longer folded.

### R31.14 A raising call with the receiver open

`AddLast(node)` calls the static `ValidateNewNode(node)`, which reads `node.list` and so
takes the list's region, which the receiver's invariant owns. The receiver is open around
the call, and cannot be closed around it as R27.38 closes one: the callee needs the region.
An exception the callee raises would then leave the invariant unfolded, and the method's
`raises` needs it closed.

A Pulse `try` whose handler closes the receiver and raises again does not work: Pulse adds
to every handler a branch that forwards an exception no clause matched, and that branch
must give what the `try` raises, with the receiver still open, to the method's `raises`
as it is. A `fn` defined locally has no exception destination in scope, so in one, that
branch is unreachable. The call is therefore made in a local function:
```
fn catch_1 ()
  requires B.pts_to this rep ** region h
  returns caught: option exn
  ensures B.pts_to this rep ** region h **
          pure (None? caught ==> <callee's ensures>) ** pure (Some? caught ==> <callee's throws>)
{ try ... { ValidateNewNode node; None } catch { ex -> { Some ex } } };
let t = catch_1 ();
if (Some? t) { <close the receiver, as a throw does>; raise (Some?.v t) } else { () };
```
The callee's `[Ensures]` and `[Throws]` are read at the arguments and at the heaps held.
This applies only to a static call whose arguments are names, with the receiver the only
open object and its representation nothing but its box and its regions. The receiver may
be held at a fraction.

### What is verified

The model is `Nodes` (the nodes, in order from `head`), `Items` (their values), `Count`
and `Version`. Every mutator ensures `Version == Bumped(Old(Version))`, where `Bumped` is
`version++` on a wrapping counter; the read-only members leave it unchanged.

| Member | Contract |
|---|---|
| `LinkedList()` | empty |
| `Count`, `First`, `Last` | `Count`; `Nodes[0]` or `Nodes[Count-1]`, or null when empty |
| `AddFirst(T)`, `AddLast(T)`, `ICollection<T>.Add` | the new node and item inserted at 0 or at the end; requires `Count < int.MaxValue` |
| `AddAfter(node, T)`, `AddBefore(node, T)` | inserted after or at `node`'s position; throw `InvalidOperationException` when `node` is not in the list |
| `AddFirst(node)`, `AddLast(node)`, `AddAfter(node, newNode)`, `AddBefore(node, newNode)` | the given node and its item inserted as for the value overloads, the node then owned by the list; throw `InvalidOperationException` when the node to insert has an owner (`Owner(heap, node) != null`), or when `node` is not in the list |
| `ValidateNewNode` | throws `InvalidOperationException` exactly when the node has an owner |
| `Remove(node)` | removed at `node`'s position; throws when `node` is not in the list |
| `RemoveFirst`, `RemoveLast` | removed at 0 or at the end; throw when empty |
| `Find`, `FindLast` | the node at `IndexOf`/`LastIndexOf` of the value, or null; the model unchanged |
| `Contains`, `Remove(T)` | through `IndexOf` |
| `CopyTo(T[], int)` | `array` is `Splice(old, index, index + Count, Items)`; the two argument exceptions |
| `InternalInsertNodeBefore`, `InternalInsertNodeToEmptyList`, `InternalRemoveNode`, `ValidateNode` | on `head`, `count` and the ring's shape |
| `Clear` | `Count` is 0, and `Cleared(Old(heap), heap, Old(Nodes), Old(Count))`: every old node is detached (links and owner null, item kept), and nothing else changed |
| `GetEnumerator`, `IEnumerable<T>.GetEnumerator`, `Enumerator` (constructor, `Current`, `IEnumerator.Current`, `MoveNext`, `Reset`, `Dispose`) | §28's borrowing enumerator; `MoveNext` throws `InvalidOperationException` when `Version` changed, and otherwise steps `_index` over `Nodes`; requires `Count < int.MaxValue` |
| `LinkedListNode.Next`, `Previous` | `Succ`/`Pred` of the node in its owner's ring; with the ring's shape, `Nodes[pos ± 1]` or null at the ends |
| `LinkedListNode.Value` (get and set), `Invalidate` | the node's item; `Detached` |

### Not annotated, and why

* `LinkedListNode.List`. It returns the owner, and a returned object comes with its
  invariant, which the node cannot give.
* `LinkedList(IEnumerable<T>)` (an interface enumeration), `ICollection.CopyTo(Array, int)`
  (an untyped array), serialization (`GetObjectData`, `OnDeserialization`), `ValueRef`
  (a `ref` return) and the public `LinkedListNode(T)` constructor (a node allocated outside
  any owner's region). The node-taking overloads therefore insert a node already in this
  list's region and detached from it, such as one `Remove(node)` or `Clear` detached: the
  model has no node outside every region.

### Findings (§31)

* The public members that take a node require `Pal.InRegion(node)`: the node must be in
  this list's region, though it need not be in the list. This is a limitation of the model.
  The code's `ValidateNode` turns a node of another list into `InvalidOperationException`;
  the contract can say so only for nodes in the region. Likewise `ValidateNewNode`'s
  exception is specified for a node in the region that still has an owner.
* `InternalInsertNodeBefore` and `InternalInsertNodeToEmptyList` also ensure
  `Pal.InRegion(newNode)`: `ViewsKept` says so, but it is opaque, and the overloads
  then write `newNode.list`.
* `Find(null)` and `FindLast(null)` test `item == null`, not `EqualityComparer<T>.Default`.
  The contracts' `IndexOf` follows the code.
* `CopyTo`'s contract also ensures `0 <= index && index + Count <= array.Length`, which the
  `Splice` needs to be well-typed.
* The `Value` setter's contract states the node's new item only: the effect on the owning
  list's `Items` would need the owner, which the node does not hold.
* `Find` and `FindLast` call `EqualityComparer<T>.Equals`, which the write-set scan counts
  as a possible write, so they are not read-only, and a caller would lose the list's model.
  Their contracts therefore also say that `Count`, `Nodes` and `Items` are unchanged. A
  rule treating bound members (R21.5) as pure was tried. It made `HashSet<T>.FindItemIndex`
  read-only, and that member's array reads have no read-only translation, so the rule was
  dropped.
* The `Debug.Assert`s (for example `node.list == this` in `InternalRemoveNode`) are proof
  obligations, and all of them are proved.

### Trusted (§31)

`Pulse.Lib.CSharp.RefEq.ref_eq` (R27.8) and `Null.is_null` (R25.4) were already trusted.
The harness binds `EqualityComparer<T>`, `Default` and `Equals` to
`Pulse.Lib.CSharp.Equality` (§24's modeling axioms). There is no new assumption.

## 32. SortedSet views and the rest of SortedDictionary

This section continues §27.3 (`SortedDictionary<TKey,TValue>` over `TreeSet`). Its
rules make the dictionary's key and value collections, and its explicit
`ICollection<KeyValuePair<TKey,TValue>>` members, verifiable.

### R32.1 A borrowing constructor's null guard

A borrowing class's constructor (R29.3, R28.5) may only assign its fields. dotnet/runtime's
`KeyCollection(SortedDictionary<TKey,TValue> dictionary)` first calls
`ArgumentNullException.ThrowIfNull(dictionary)`.

Under R10.2 a non-nullable class-typed parameter is never null, so the guard cannot
throw. It is skipped, as it is in any body (R23.2). A guard on a nullable or
non-class argument is still refused (PALCS0730).

### R32.2 `[Frac]` methods are read-only to their callers

`Declarations.IsReadOnly` decides whether a caller may hold an object at a fraction across
a call. An interface call (an `IComparer<T>.Compare`) counts as possibly mutating, because
the callee is unknown.

A concrete method marked `[Frac]` (R27.24) is checked by R4.11c to need only a fraction of
its receiver, so it is read-only whatever it calls. `IsReadOnly` now says so, which is
what the front end's own test already did. Without this rule:
- `SortedDictionary.ContainsKey` (which calls `SortedSet.Contains`, a `[Frac]` method calling
  `comparer.Compare`) was taken to mutate the dictionary;
- so `KeyCollection.Contains`, a borrowing member holding the dictionary at a fraction,
  could not call it.

### R32.3 The default equality in the SortedSet harness

`EqualityComparer<TValue>.Default.Equals` is bound in `pal/SortedSet/Bindings.cs` exactly as
in the hashing harness: the type to `Pulse.Lib.CSharp.Equality.comparer`, `Default` to
`default_comparer`, and `Equals` to `equals`. The library lemma `default_equals_def` turns
`equals (default_comparer t) x y` into R22.25's `default_equals x y`, which contracts write
as `Pal.DefaultEquals(x, y)`. No new trust is added: these are the hashing harness's
bindings, reused.

### R32.4 Two emitter fixes for holders

Both appeared in `SortedDictionary`'s explicit `ICollection<KeyValuePair<,>>.Remove`.

- **Tuple parameter cells.** A by-value parameter that becomes a cell (R4.2) of tuple type
  (a `KeyValuePair`) is declared with its type, `let mut x : tuple2 a b = arg_x`, as a local's
  cell already was. Otherwise the tuple's universe is inferred, and `let mut` needs it to be
  zero.
- **Open fields in tail `if` arms.** A field a call left open at a heap (R27.59) and one arm
  of a tail `if` closed was taken as closed in the other arm as well. That arm then
  returned without closing it. Each arm of a tail `if` (including R10/R24 null windows) now
  starts from the open fields as they were before the `if`.

### R32.5 Anonymous methods as callbacks

A `[Callback]` argument (R27.39) may be an anonymous method,
`delegate (Node node) { … }`, as well as a lambda. dotnet/runtime's
`SortedDictionary.ContainsValue` passes two. Both are lifted to the same function, with
the same captures and protocol (`Pal.Protocol`, R27.39); an anonymous method's parameter
list must be present and have one parameter.

### R32.6 A callback passed in a non-tail `if` arm

What a walk ensures of its callback's trace, and so of the captured locals the protocol
names, is stated over an existential trace. Pulse's join after a non-tail `if` keeps only
one arm's existential facts. An `if` with an arm that passes a lambda to a `[Callback]`
parameter is therefore one whose join loses (R22.12): the rest of the block is moved into
both arms. `ContainsValue`'s `if (value == null) walk(…); else walk(…); return found;` needs it.

### R32.7 Binding a field of an unmodelled class

`SortedDictionary.Comparer` reads `((KeyValuePairComparer)_set.Comparer).keyComparer`. The
pair comparer is modelled as `KeyComparer`'s comparer of pairs, from which `key_of` recovers
the key comparer (§27.3). The harness binds the field
`KeyValuePairComparer.keyComparer` to `key_of`, and the downcast is the identity, as both
types are the same F* type. Both are trusted (they hold because the dictionary's
constructors build the set's comparer from the key comparer and nothing else).

### R32.8 Searching values

`Pulse.Lib.CSharp.ValueSearch` (C# `SpecValueSearch`) states `ContainsValue`:

- `Matches(x, y)` is `x == null` when `y` is null and `Pal.DefaultEquals(x, y)` otherwise, as
  the method tests it;
- `HasValue(pairs, y)` is whether some pair's value matches `y`;
- `Searched(tr, y, found)` is the callback's protocol: each call returned false exactly on a
  match, and `found` says whether one was made.

Its lemmas (with SMT patterns) take the protocol from the empty trace, through one call,
to the walk's end, where `found == HasValue(pairs, y)`. `ContainsValue` and
`InOrderTreeWalk` are `[Frac("p")]` (R27.24), so that the borrowing
`ValueCollection.Contains` (R29.3) may call `ContainsValue`; by R32.2 the walk's callers
(the `SortedSet.CopyTo` overloads, `SortedDictionary.CopyTo`) become read-only too.

### R32.9 A read-only holder's call on its owned field

Under R32.2 a method of a holder (R27.58) whose calls are all read-only holds its receiver
at a fraction. A call that may raise from such a method closes the objects held at a
fraction around it, so that the raise leaves them whole. The receiver is not one of
them when the call's receiver is its own owned field: that field's invariant is opened from
the receiver's, so closing the receiver would need the field closed first.
`SortedDictionary.CopyTo` (whose `_set.CopyTo` may raise, but whose `Requires` rule it out)
needs it.

### R32.10 Writing through a node an owned field's search found

A spec-only struct may hold a pointer to a `[Region]` class: it is a value that owns
nothing (PALCS0511 is not reported for it). A region owner's model can then name its root
(`SortedSetModel.Root`, `[Spec] internal SpecRoot`), and a search's contract can say that
the node it returns is one of the tree's nodes:
`SpecRegionWrite.InTree<Node, T>(Pal.Heap<Node>(), @this.SpecRoot, Result)`
(`Pulse.Lib.CSharp.RegionReplace.in_tree`: the box is among those the root reaches).

A holder (R27.58) keeps the field open at the heap the call returned (R27.59). When the
method then writes a field of a region object, the field is marked as written. When the
field is closed, its invariant is folded at the heap the region holds then, and at the model
that heap and the field's record determine (`abs_model`). That fold is the proof obligation
that the write kept the owner's invariant and its `[Refine]`s. It is discharged by
`RegionReplace` lemmas that fire on their own:

* `write_unshared` and `write_in_tree`. A write to a node of the tree that keeps the node's
  links leaves the tree unshared. The in-order keys change only at the node's position (`pos`),
  where the old key was. If the write keeps the node's colour, the shape, size and
  red-black colouring are unchanged.
* `upd_equiv`. Replacing a key with one that compares like it keeps a strictly sorted
  sequence strictly sorted.
* `key_index_index`. In a strictly sorted sequence, an element's key index is its position.

The `SortedDictionary` indexer setter replaces the value of the pair a search found
(`node.Item = new KeyValuePair(node.Item.Key, value)`). Its contract says the pairs are
updated at the key's index when the key is present, and that the pair is inserted otherwise.
`Pal.SetAt` takes a `SpecInt` index.

### R32.11 A callee-stated bound on a callback's calls

A walk calls its callback once per node, and a callback that writes `array[index++]` with
no check of its own needs to know that. The R27.39 callback type bounds the trace only by
its call budget (`max_calls`), so it cannot. A `[Callback]` parameter can take a bound:

* The callee declares `[Callback(Bounded = true)]` and states what it calls back fewer
  times than, in a precondition over `Pal.CallBound(action)`. For example, the walk has
  `[Requires("@this.SpecItems.Length <= Pal.CallBound(action)")]`. `Pal.CallBound`
  names a `[Callback]` parameter of the enclosing method, else PALCS0800.
* The bound is a ghost argument the caller chooses (`n_action: erased int`, before the
  action). The callback's type `region_cb view p n` requires `|tr| < max_calls` and
  `|tr| < n` of the trace each call extends.
* A lambda states its bound as the second argument of `Pal.Protocol(tr => …, bound)`. The
  lifted method (`bound_L`, of the lambda's type parameters and captures) is passed for
  `n`. The lambda may then assume `|tr| < bound` on entry. The bound may name only
  captures the lambda does not write, so it is fixed when the lambda is passed. A bound
  given to an unbounded parameter, or one that names a written capture, is PALCS0800.
* A lambda with no bound passed to a bounded parameter, and every lambda passed to an
  unbounded one, gets `max_bound` (`max_calls`), the old budget.

Lambdas in the members of a borrowing class (R29, e.g. `KeyCollection.CopyTo`) are now
lifted like those of other classes. Before, their lifted methods were dropped.

`Pulse.Lib.CSharp.PairWalk` states what a walk of pairs copied (`copied_keys`,
`copied_values`, of `KeyMap.keys`/`KeyMap.values`) and proves it from the trace. With the
walk's bound set to the pair count, the views' `CopyTo` write `array[index++]` in range,
and their contents become the old contents spliced with the keys or values from `index` on.

### R32.12 Wrapping structs

`SortedDictionary.Enumerator` holds a `SortedSet<KVP>.Enumerator`, and the key and value
enumerators hold a `SortedDictionary.Enumerator`. A *wrapping struct* is a struct, not
itself borrowing (R28.1), with exactly one field whose type is a borrowing or wrapping
struct (its *wrapped field*). Its other fields are primitive. Following wrapped fields
leads to one borrowing struct, its *core*.

* A wrapping struct's members are translated as members of the core's owner. They take
  the owner (`this`), the wrapping struct as `self` (by reference if the member writes it),
  and the objects the core owns (R27.41). The member requires and ensures that
  `self`'s path to the core borrows exactly these, and that each readonly field along
  the path is unchanged.
* In a member, `_inner.M(…)` is a call of the core's member (or of the next wrapper's) on
  `self._inner`. A call that writes the wrapped struct copies the field to a local
  (`__pal_innerN`), passes the local by reference, and writes it back to the field after
  the call. A raise skips the write-back. That is sound because a struct's state after a
  raise is existential. In a `try` a handler could see the field before the call, so the
  call is refused there (PALCS0802).
* Contracts may name the wrapped struct's `[Spec]` members (`_inner.SpecWalking`), which
  are inlined at `self._inner`; its private fields are not visible to them.
* The constructors of a wrapping struct, and `new W(…)` of one, are refused (PALCS0801).
  Building the core needs its owner, and the dictionary's enumerator gets it from
  `dictionary._set.GetEnumerator()`: a holder cannot expose the region heap of the set it
  owns, so the caller cannot be told what the new core borrows.
* `if (_inner.Test()) throw …;` in such a member nests the rest of the body in the `else`
  arm, as R27.38 does for owners, so that the rest knows the call's result was false.
* The owner's type parameters in the region heaps a member takes are those of `this`'s
  type: the dictionary's members hold `SortedSet<KeyValuePair<TKey,TValue>>`'s node heap at
  `Node<(TKey & TValue)>`.
* A `has_default` need (R22.22) at a compound type argument (`KeyValuePair<TKey,TValue>`)
  is a need at each type parameter inside it, since the instance is built from theirs.
* When the core is generic and instantiated at a compound type, the copy `__pal_innerN`
  has the core's nominal type while the core member's post-state is typed at the unfolded
  refinement. F* gives the two refinements distinct SMT symbols, so nothing links the copy
  to the result. The module gets a *reveal bridge* for each such type: a lemma, proved by
  `trefl`, that the two `reveal`s of the same erased value are equal, triggered on the
  nominal one.

### R32.13 Views

`SortedSet<T>.TreeSubSet` is a *view*: a `sealed` class nested in a generic class `B` with a
`[Model]`, deriving from `B`, with no `[Model]` of its own and one readonly field typed at `B`
(the *underlying* object, assigned from a constructor parameter). It is translated as an
R29.3 borrowing class of `B`:

* Its record holds its own fields and the instance fields it inherits from `B`. A field of
  `B` with no translation is left out (R25.3), as is `B`'s comparer's null-ness: the
  comparer is a value (R27.47) and so may be held.
* Its members are methods of `B` that take the underlying object as `this` and the view's
  record as `self`, always by reference. A member that calls, transitively through the
  view's own members, a member of the underlying object that is not read-only holds the
  underlying object exclusively; otherwise it holds it at a fraction.
* *Static binding.* A view never exists as an object of `B`: a method returns one only
  under `[return: Exactly(typeof(B<>.V))]`, and a caller holds the result in a local (as it
  holds a borrowing struct, R27.41). So every call on a view binds statically, by exact
  type: to `V`'s override when `V` declares one, and otherwise to a *replica* of `B`'s
  member. A replica is the member's body lowered again at `V` (`V_at_B_M`), so its own
  calls on `this` bind at `V` in turn, and `base.M(…)` inside a member of `V` is the
  replica of `B.M`.
* *Contracts at a view.* `[Requires]`/`[Ensures]`/`[Throws]` take `At = typeof(B<>.V)`. A
  clause with `At` is a clause of the member's replica at `V` only; one without is a clause
  of `B`'s own member only. In such a clause `@this` is the view, and both its own `[Spec]`
  members and the underlying object's (`@this._underlying.SpecItems`) may be named; `B`'s
  `[Spec]` members on the view are refused (PALCS0803), since they read `B`'s model, which
  a view does not have. An override of `V` with no contract of its own takes the `At`
  clauses of the member it overrides. This needs no behavioural subtyping: no call
  dispatches dynamically between `B` and `V`.
* Every member requires and ensures that `self`'s underlying field is `this`, and that its
  readonly scalar fields are unchanged. A method returning a view ensures that the view's
  underlying field is its receiver, so a caller's view local is known to borrow it.
* A view's constructor is `: base(…)` followed by assignments. The base constructor is
  inlined: its arguments are bound to locals, and its body must be assignments to fields,
  which become the record's initial values (else PALCS0804). A later read of a field
  already assigned reads the assigned value.
* A `[Spec]` member of `V` named on a call's result (`Result.SpecLo`) is inlined at the
  result, with `B`'s receiver as the underlying object.

`test/sortedset/View.cs` is the test: a view with a write-through override, a replica
reached through a virtual call, and a version check, used from methods of the base.

### R32.14 Views used from the base, and writes through them

R32.13 translates a view. This section adds what the base's members need in order to use a
view, and what a view needs in order to write through to the underlying object.

* *The base's `this as V` (absent views).* A member of `B`, verified at `B`'s exact type
  (R27.1), may declare `V? x = this as V;` and never write `x`. The receiver is then a `B`
  exactly, never a view. So `x` is recorded as absent: `x == null` is `true`, and
  `x != null` is `false`. This holds outside a view's own members and replicas, where
  `this` may be a view. `SortedSet.UnionWith` and `IntersectWith` test their receiver so.
* *Scope.* A view's override is checked against the member it overrides only when that
  member has a clause `At` the view. Overrides with no such contract (e.g. `Clear`, the
  walks) stay untranslated, and nothing at the view may call them.
* *Frame.* A view's member ensures that it leaves unchanged every field of its record
  that it never writes. That covers the view's own fields and those it inherits from `B`.
  A field counts as written when the body assigns or steps it, or passes it by `ref`. It
  also counts when a member reached on `this` does so, including properties read or
  written and lambdas written in those bodies, bound at the view and taken transitively.
  So `Contains` at a view is known to keep `_min`/`_max` and the inherited `comparer`.
* *Default arguments.* A call on a view (or of a replica) supplies the callee's default
  arguments, as `VersionCheck()` relies on.
* *Shared reference to self at a join.* A view's member holds its record by reference.
  At an `if` whose arms both pass the record by reference, the two arms' facts about the
  record are joined after the `if`. Pulse loses them there, so such an `if` is split into
  two copies, each carrying the code that follows it, as R22.12 does for joins that would
  lose facts.
* *Ranges (library).* `Pulse.Lib.CSharp.SearchTree.range_root c t min max lo hi` is the
  subtree a range search (`FindRange`) stops at: the first node whose item is in the
  range, or `Leaf`. `SpecSearchTree.RangeRoot` and `InRange` name it and its range test.
  The lemmas show that a search for an in-range item from `range_root` finds it iff the
  whole tree has it. `FindRange` ensures that its result is the range root, and is
  `Unshared` (no other node points to it). That lets a view keep the root without the
  rest of the region.
* *Casts to a view in contracts (`((V)x)`).* Take a local typed at `B` that holds a view
  of exactly `V`, from an Exactly-return (R32.13). In a contract or loop invariant,
  `((V)x).SpecM` names `V`'s `[Spec]` members on the view it holds. This is how
  `IsSubsetOf`'s loop states the view's coherence. A cast of anything else is refused as
  before.
* *Views of another object.* `other.GetViewBetween(…)` on an object other than `this`
  yields a view that borrows `other`'s region. It is held at `other`'s heaps, like
  R32.13's views of `this`, and not as a plain local.
* *Returns inside nested ifs.* For `if (a) { if (b) return e; } rest`, the code after the
  `if` (`rest`) is copied into its arms, as for a `return` inside a loop (R24.14, R26.2). Before,
  this was PALCS0001.
* *Write-through and the version (library `Pulse.Lib.CSharp.Wrap`).*
  `SpecWrap.Int32(n)` is `n` wrapped to 32 bits, the value a `[Wrapping]` `version++`
  leaves (lemma `int32_add_wrap`).
  * `SortedSet.Add`/`AddIfNotPresent` ensure `version == Int32(old version + 1)`.
  * `Remove`/`DoRemove` ensure the same when the set was non-empty, and an unchanged set
    and version when it was empty.
  * A view's write-through (`AddIfNotPresent`, `DoRemove`) requires that the view's
    version is not `Int32(set's version + 1)`: see §32 Findings. Given that, the view's
    stale root is never mistaken for current. The re-check that follows (`VersionCheck`)
    re-establishes coherence: a version equal to the set's implies that the root is the
    range root of the set's tree.
* *`SerializationInfo` (request (b)).* It needs no new rule. A field or member whose type
  does not translate is left out (R25.3), and no translated member reads it.
  `GetObjectData`/`OnDeserialization` are not translated (§32 Not verified).
* *Subset family (library `Pulse.Lib.CSharp.SetOps`).*
  * `all_in c s t` holds when every item of `t` is a member of `s`, with lemmas for one
    step, the whole sequence, a length bound, and the bounds of a sorted sequence.
  * `SpecSetOps.AllIn`/`AllInStep`/`AllInWhole`/`AllInLength`/`SortedBounds` name them.
  * `IsSubsetOfSortedSetWithSameComparer` walks this set while checking membership in a
    view of the other set, restricted to this set's min and max. Its loop invariant
    states that the visited prefix is `AllIn` the other set.

`test/sortedset/View.cs` adds the tests:
* `CountAboveOf`: a view of another object, used in a loop invariant through `((Top)v)`.
* `Nested`: a nested `return`.
* `Kind`/`Pick`/`Current`: an absent view, a join, and a default argument.

### Verified (§32)

`SortedDictionary<TKey,TValue>` members verified in this section:

| Member | Contract |
| --- | --- |
| `Keys`, `Values` (view-cache fills, R29.3b) | `ReferenceEquals(Result._dictionary, this)` |
| `KeyCollection(d)`, `ValueCollection(d)` | `ReferenceEquals(_dictionary, d)` |
| `KeyCollection.Count`, `ValueCollection.Count` | `_dictionary.SpecPairs.Length` |
| `KeyCollection.Contains(k)` | `KeyIndex(keys, k) >= 0`; throws `ArgumentNullException` on a null `k` |
| `ICollection<T>.IsReadOnly` (both views) | `true` |
| `ICollection<T>.Add`/`Clear`/`Remove` (both views) | always throw `NotSupportedException` |
| `ICollection<KVP>.IsReadOnly` | `false` |
| `ICollection<KVP>.Add(p)` | as `Add(p.Key, p.Value)`: requires the key absent and below `int.MaxValue` pairs |
| `ICollection<KVP>.Contains(p)` | the key is present, and its value is null when `p.Value` is null, else `DefaultEquals` to it |
| `ICollection<KVP>.Remove(p)` | `Result` iff the key is present with a `DefaultEquals` value; the pairs are then `Removed(p)`, else unchanged |
| `ContainsValue(v)` | `SpecValueSearch.HasValue(pairs, v)`; pairs unchanged |
| `ValueCollection` `ICollection<T>.Contains(v)` | `HasValue` of the dictionary's pairs |
| `Comparer` | the key comparer (`SpecKeyComparer`) |
| `KeyCollection.CopyTo(a, i)`, `ValueCollection.CopyTo(a, i)` | `a` spliced at `[i, i + Count)` with the keys (values) in order; throws `ArgumentOutOfRangeException` on `i < 0`, `ArgumentException` when `a.Length - i < Count` |
| indexer setter `this[key] = value` | key present: pairs `SetAt` the key's index to `(key at that index, value)`; absent: `Inserted`; requires a non-null key and fewer than `int.MaxValue` pairs |
| `Enumerator.MoveNext` (R32.12) | as `SortedSet.Enumerator.MoveNext`: fail-fast on a stale version; `Result` iff items were pending; the pending items lose their head, which is the new current key |
| `Enumerator.Current` | the current node's pair, once started and not ended |
| `Enumerator.Reset`, `IEnumerator.Reset` | fail-fast on a stale version; pending is the whole in-order sequence again |
| `Enumerator.Dispose`, `NotStartedOrEnded` | nothing; `Result` iff the walk has no current node |
| `IDictionaryEnumerator.Key`/`Value` | throw `InvalidOperationException` when not started or ended |
| `KeyCollection.Enumerator`, `ValueCollection.Enumerator`: `MoveNext`, `Current`, `IEnumerator.Current`, `IEnumerator.Reset`, `Dispose` | as the dictionary's enumerator, projected to the key (value); `IEnumerator.Current` boxes it (`Pal.Boxes`) and throws when not started or ended |
| `IDictionary.IsFixedSize`, `IDictionary.IsReadOnly`, `ICollection.IsSynchronized` (dictionary and both views) | `false` |

`ContainsKey`, `TryGetValue` and `SortedSet.TryGetValue` were re-verified under R32.2.
`InOrderTreeWalk`, `RemoveWhere`, the three `SortedSet.CopyTo` overloads and
`SortedDictionary.CopyTo` were re-verified with the walk `[Frac]` (R32.8, R32.9).

`SortedSet<T>` and `TreeSubSet` members verified under R32.13/R32.14. Here *coherent* means
that the view shares the set's comparer and, when its version is the set's, its root is
`RangeRoot` of the set's tree.

| Member | Contract |
| --- | --- |
| `GetViewBetween(lo, hi)` | throws `ArgumentException` when `lo > hi`; the view has bounds `lo`/`hi`, both active, its root is the range root, and it is coherent; the set is unchanged |
| `TreeSubSet` constructor | the fields are the arguments, `version == _countVersion == -1`, and the root is the range root |
| `IsWithinRange(x)` | `InRange` of the bounds |
| `TreeSubSet.TotalCount()` | the underlying set's item count; the set is unchanged |
| `VersionCheck()`, `VersionCheckImpl(false)` | coherent and current afterwards (version is the set's, root is the range root) |
| `TreeSubSet.Contains(x)`, `FindNode(x)`, and the replicas of `SortedSet.Contains`/`FindNode`/`Comparer` | `x` is in range and in the set (`FindNode`: non-null iff); coherence kept |
| `TreeSubSet.AddIfNotPresent(x)` | out of range: throws `ArgumentOutOfRangeException`; else as the set's `AddIfNotPresent`, the view coherent and current; requires the version precondition (Findings) |
| `TreeSubSet.DoRemove(x)` | `Result` iff in range and present; in range: the set's items are `Removed(x)`, else unchanged; coherence kept under the version precondition |
| `SortedSet.Add`, `AddIfNotPresent`, `Remove`, `DoRemove`, and `TreeSet.AddIfNotPresent`/`Add` (strengthened) | additionally the version moves to `Int32(old + 1)` on a write and stays put on `Remove` from an empty set |
| `IsSubsetOfSortedSetWithSameComparer(other)` | `Result` iff `AllIn(c, other.items, items)`; both sets and comparers unchanged |
| `IsSubsetOf`, `IsProperSubsetOf`, `IsSupersetOf`, `IsProperSupersetOf` (same-comparer `SortedSet` branch) | requires the same comparer; `AllIn` of the two sets' items in the direction named (and, for the proper forms, a strict size inequality) |
| `UnionWith`, `IntersectWith` (re-verified) | as before (R32.5), with `this as TreeSubSet` absent (R32.14) |

### Trusted (§32)

* The R32.3 `EqualityComparer` bindings (the hashing harness's).
* The R32.7 binding of `KeyValuePairComparer.keyComparer` to `key_of`, and the downcast to
  `KeyValuePairComparer` as the identity.

### Not verified (§32)

* The `ICollection.CopyTo(Array, int)` forms (of the dictionary and both views). They test
  `array.Rank` and `GetLowerBound`, type-test `array` (`is TKey[]`, `as object[]`) and
  rely on array covariance raising `ArrayTypeMismatchException`. None of these is modelled.
* The enumerators' constructors and the `GetEnumerator`s that call them, and the
  `IDictionary` constructors: the core is built by `dictionary._set.GetEnumerator()`, and a
  holder cannot expose the region heap of the set it owns (R32.12).
* The dictionary enumerator's `IEnumerator.Current` and `Entry`: they build a
  `DictionaryEntry`, which is not modelled.
* The other non-generic `IDictionary`/`ICollection` members (`this[object]`, `Add(object,
  object)`, `Contains(object)`, `Remove(object)`, `SyncRoot`): they type-test `object`
  keys and values (`is TKey`) and cast them, catching `InvalidCastException`; neither is
  modelled for type parameters.
* `TreeSubSet` members other than those verified above (R32.14):
  * `Clear` builds a `List<T>` of the in-range items in a breadth-first walk lambda, then
    removes them through the set. Its contract would need the walk's per-element trace
    over a queue of region pointers (R32.9 covers only the in-order walk).
  * `InOrderTreeWalk`/`BreadthFirstTreeWalk` overrides: range-pruned walks over a
    `Stack<Node>`/`Queue<Node>`. They would need R32.11's bounded walk restricted to
    `range_root`.
  * The re-count `VersionCheckImpl(updateCount: true)`, and so `Count`, `MinInternal` and
    `MaxInternal` at a view.
    * The re-count's lambda writes the view's `count` while the walk holds the view (a
      PALCS0579 cycle), so `VersionCheckImpl` requires `!updateCount`.
    * `MinInternal`/`MaxInternal` are reached only through `Min`/`Max`, which read
      `Count` first.
  * `InternalIndexOf`: it enumerates the view (`foreach (T i in this)`), and a view's
    enumerator is a borrowing struct of a borrowing class, which is not translated.
  * `GetViewBetween` on a view returns a view of the *underlying* set. R32.13's
    Exactly-return contract makes the result borrow the receiver, so a view of a view's
    underlying set is not expressible.
  * `GetObjectData`/`OnDeserialization`: their `SerializationInfo` parameter does not
    translate (R25.3). They only throw `PlatformNotSupportedException`.
* `IsSubsetOf`/`IsSupersetOf` and their proper forms on an `IEnumerable<T>` that is not a
  same-comparer `SortedSet<T>`: they go through `CheckUniqueAndUnfoundElements` (BitHelper,
  §27 Findings).

### Findings (§32)

* `ICollection<KVP>.Contains` and `Remove` disagree on null values. `Contains` tests a
  null `p.Value` with `== null`, but `Remove` always calls
  `EqualityComparer<TValue>.Default.Equals`. These agree for the default comparer, but
  the contracts state each as written.
* `ICollection<KVP>.Add`, like `Add`, requires the key to be absent: a holder cannot pass on
  the exception its owned set raises (§27.3).
* A view's "never checked" versions can collide with the set's. `TreeSubSet`'s
  constructor sets `version` and `_countVersion` to `-1` as sentinels. But the set's
  `version` is `[Wrapping]` and so can itself be `-1`. If it is `-1` when the view is
  created, `Count` (`VersionCheck(updateCount: true)`) skips the recount and returns 0
  however many elements are in range. If it is `-2`, one modification makes it `-1`, the
  versions agree, and the view keeps the `root` it found before the modification, which may
  be a removed node. Both need about 2^32 modifications first. The contracts therefore
  cannot let a view's count or root rest on version equality alone.
* Writes through a view rest on a version precondition. `TreeSubSet.AddIfNotPresent` and
  `DoRemove` write the set, which moves its version to `Int32(v + 1)`, then call
  `VersionCheck`. That re-finds the root only if the view's version differs. If the view's
  version already equals `Int32(v + 1)`, the view keeps its old root, which is stale. That
  happens with the `-1` sentinel when the set's version is `-2`, or with a view
  re-synchronised about 2^32 writes earlier. Its later `Contains`/`FindNode` then search
  the wrong subtree, and may follow a node the write removed. The contracts say so
  honestly: both writes require `version != Int32(underlying.version + 1)`. The
  precondition is what coherence needs, and nothing stronger.

## 33. `OrderedDictionary<TKey,TValue>` and leftovers

dotnet/runtime's `OrderedDictionary<TKey,TValue>` (System.Collections) is verified in place
by the harness `pal/OrderedDictionary`, against a functional model: the keys and the values
as sequences in insertion order, and the comparer. Its table is the separate-chaining
table of `Dictionary`/`HashSet` (`Pulse.Lib.CSharp.HashChain`) without a free list: every
entry below `_count` is live, and removal shifts the later entries down. The glue theory
(`OrderedDictionaryChain.fst`) states the table's well-formedness `wf` and the chain walk
`search` as opaque predicates, reached only through lemmas; with them transparent, the
lookup's queries did not finish in 15 minutes, and opaque they take seconds.

The test `test/ordereddict` exercises each rule below.

**R33.1. System.Collections' guard polyfills.** System.Collections compiles its own
`ThrowHelper.ThrowIfNegative`, `ThrowIfLessThan` and `ThrowIfGreaterThan` where the BCL's
`ArgumentOutOfRangeException.ThrowIfNegative` (R23.2) is missing. A call of one of them on
an integral argument is read as the BCL guard: `if (x < 0) throw ...`.

**R33.2. Forward `goto`.** `goto L;` where `L` labels a statement of the method's outermost
block after the jump, and the code from `L` to the end of that block cannot run off the end
of the method, is that code, copied to the jump. A local of the outermost block declared
between the jump and the label, and used from the label on, is declared (uninitialised) at
the jump; C#'s definite assignment makes the copied code assign it before reading it. A
labelled statement that the statement before it cannot fall into — by C#'s reachability, or
because that statement is a call of a `[DoesNotReturn]` method — is reached only by jumps,
so it and what follows are not lowered where they stand. A backward jump, a jump out of a
`try`, lambda or local function, and a jump whose tail can fall off the method are reported.

**R33.3. Inlined `ref` helpers.** R24.9's inlining of a `ref`-returning method also skips
`Debug.Assert` statements among its locals, and accepts a body ending in
`if (c) return ref a[i]; else return ref a[j];` into one array `a`, which is `a[c ? i : j]`
(`GetBucketRef`'s two arms for 32- and 64-bit).

**R33.4. Bound machine-integer members.** A `[SpecBinding]`-bound property or field of a
machine-integer type (`IntPtr.Size`, bound to `Pulse.Lib.CSharp.Platform.intptr_size`) is
a machine integer: in code it is the bound value, and in a specification its mathematical
value (`.v`).

**R33.5. Rebound `ref` locals.** A `ref` local that is rebound (`x = ref a[e];`), where
every binding (and the initialiser, unless it is `ref Unsafe.NullRef<T>()`) is an element
of one array `a` named by a local never assigned or by a field of `this` that the scope
neither assigns nor can replace by a call, is a mutable index into `a`: each binding
assigns the index, and each use of `x` is `a[index]`. A null reference is index `-1`, so a
use of it is an out-of-bounds access the proof must rule out. The array may be declared
after `x`; the uses are lowered where they occur.

**R33.6. `is null` on an array.** `a is null` and `a is not null` on an array are R24.7's
`a == null` and `a != null`. They were folded to the constants `false` and `true`, as for a
non-nullable value — a soundness bug (see Findings).

**R33.7. Arguments nobody reads back.** An `out _` discard is a fresh local, initialised
to its type's default, passed by reference. So is a `ref x` argument when an earlier
argument of the same call also passes `ref x` (`IndexOf(key, ref _, ref _)`, with `_` a
local), provided `x` is used nowhere else in its method and the callee's parameter is only
ever assigned (reads inside `Pal` intrinsics, which are ghost, aside). Pulse cannot pass
one reference twice; under these conditions the aliasing is unobservable — the callee never
reads the parameter, and nothing reads `x` afterwards — so separate locals behave alike.
Any other repeated `ref` is reported, as before.

**R33.8. `a?.Length ?? d` on an array.** It is `a == null ? d : a.Length` (R24.7), when `a`
has no effects.

**R33.9. `out var` in an `if`'s condition.** `if (!TryGetValue(key, out TValue? value)) …`
declares `value` in the enclosing block, as C# scopes it: the declaration is hoisted ahead of
the `if` at its type's `default`, as R27.43 does for a loop's condition. The call writes it
before anything reads it.

**R33.10. A write through a local array is a write.** R4.11 decides whether a method leaves
its receiver's model unchanged by scanning its body. An element written through a local
array (`nodes[i] = x` after R24.19's `T[] nodes = _nodes;`) now counts as a write, unless
every value the local takes is a new array (an array creation or a collection expression,
never passed by `ref`). `PriorityQueue`'s `MoveDown*` had been classified as mutators only
because they call a comparer; had they not, the emitted code would not have verified, so
the gap was incompleteness, not unsoundness.

R33.14 completes this in the other direction.

**R33.11. `x ??= d;` on a local or parameter** is `x = x ?? d;`, `x` read once (it is a
variable). For a comparer, whose null the model cannot see (R25.4), it is
`x = (is_null x ? d : x)`; for an `option` it is `x = (Some? x ? x : Some d)`. When `d`'s type
is another C# type bound to the same F* type (`EqualityComparer<T>.Default` for an
`IEqualityComparer<T>?`), the `Some` is given the option's type. A field's `??=` is still
R29.3b's view cache or nothing.

**R33.12. An explicit accessor is named by the interface accessor it implements.** R29.4 names
an explicit non-indexer getter by its property; any other explicit accessor -- an explicit
indexer's `get_Item`/`set_Item`, an explicit property's setter -- is named by R28.2's rule
applied to the accessor it implements: `IList1_get_Item`, `IReadOnlyList1_get_Item` and
`IList_get_Item` when a view implements all three, plain `set_Item` when it is the only one.
Before, the module and the spec shim were named by C#'s metadata name
(`System.Collections.Generic.IList<TKey>.get_Item`), which is no identifier and no shim.

**R33.13. Expression-bodied indexers and constructors.** `T this[int i] => e;` is an indexer
whose getter is `e`; it has no accessor to carry a contract, so the contract is written on
the indexer, as R9.20 has it for `T P => e;`. Before, it was skipped -- and an annotation on
it silently dropped. `C(T v) => _f = v;` is the constructor `{ _f = v; }`; before, the
arrow was not read at all and the constructor was translated as assigning nothing (refused
by the verifier, not unsound, but every expression-bodied constructor was unprovable).

**R33.14. What does not write.** R4.11's scan now separates reads from writes in three
places:

* a call of a `[SpecBinding]`-bound instance method (a comparer's `Equals`, `GetHashCode`,
  `Compare`) is an F* term and cannot write; its array arguments are still checked;
* a call of `Pal`'s intrinsics or of a `[Spec]` or `[Lemma]` member is ghost, and reads the
  array it is handed (`Search(Pal.Contents(_buckets), …)`);
* an assignment through a `ref` local (`entry.Next = …` after `ref Entry entry = ref
  entries[i]`) is a write, as R24.8 translates it; rebinding the local (`entry = ref …`) is
  not.

So `HashSet.FindItemIndex`, `Stack.CopyTo` and `OrderedDictionary`'s `IndexOf`,
`ContainsKey`, `ContainsValue` and `TryGetValue` are read-only, and the views (R28.2), which
hold the dictionary read-only, can call them. Two things the read-only translation then
needed:

* R27.38 reopens a read-only receiver around a raising call in a loop, which leaves the
  record existential and the measure unable to name a field's length. A `[DoesNotReturn]`
  callee (`ThrowHelper.ThrowInvalidOperationException_…` inside `FindItemIndex`'s loop) no
  longer counts: nothing after it runs.
* R23.6's `Debug.Assert(array != _array)` between a whole array and a field held at a
  fraction: `QueueStack.distinct` takes either at any permission when the other is whole
  (gathering them would exceed 1).

**R33.15. `[Open]` on a class that owns arrays.** R27.23's `[Open]` was defined for region
owners: the callee takes the receiver's record and its heaps. A class whose invariant hides
arrays (`OrderedDictionary`'s `_buckets` and `_entries`) needs the same thing for helpers that
run while the invariant is broken (`UpdateBucketIndex`, `PushEntryIntoBucket`). Such a callee
now takes

* the record, `B.pts_to this pre_this`, as before;
* for each array field `f`, `A.pts_to (reveal pre_this).f pre_this_contents_f`, and in the
  contract `this.f` denotes those contents (R3.10a) and `Pal.Contents(this.f)`'s reference is
  the record's field; the post holds each at an existential;
* for each field the body does not assign, with no call on the receiver that might,
  `post_this.f == pre_this.f`, which is what lets the caller fold again.

The caller side is R4.10's bracket: a call of an `[Open]` method on the receiver counts as
touching a field, so an ordinary method opens its invariant around it and refolds after. A
loop inside an `[Open]` method carries each array field by its own `pts_to` (R5.12), fixed if
the loop writes no element of it.

**R33.16. A `ref` local into a field's array, passed by `ref`.** `ref Entry entry = ref
entries[i]; PushEntryIntoBucket(ref entry, i);` hands the callee an element of an array the
receiver owns. The element is copied into a mutable local before the call and written back
after it (`write entries i (!entry)`), so the callee's contract about `entry` becomes one
about `Pal.Contents(_entries)[i]`: the contents after the call are the contents the callee
left, updated at `i` with the element it returned. A join where one arm replaces the
`[Open]` receiver's record keeps the arrays it owns reached through the record (rather than
through a record Pulse generalises afresh), and the array slots are restored between the
arms of a tail `if`.

**R33.17. Re-reading a field into its local copy.** R24.19's `T[] a = _a;` is refused when
something after it may replace `_a`, unless the very next statement of the block is
`a = _a;`. `entries = _entries;` after `Resize(...)` in `TryInsert` is that statement: the
local is the field again from there on, and R33.10's writes through it are writes of the
field.

**R33.18. Calls of empty methods.** Under `[TranslateAnnotatedOnly]`, a call of an
unannotated method whose body is empty (after preprocessing: `RehashIfNecessary` without
`SYSTEM_COLLECTIONS`) does nothing and is dropped, rather than refused as a call of an
untranslated method. Its arguments must be names or literals passed without a conversion: an argument
under one (R17.7's implicit borrow, say) is still lowered, so that its diagnostic is not lost.

**R33.19. `default` of a struct with a type-parameter field.** `default(Entry)`, where
`Entry` has fields of type `TKey` and `TValue`, is `Inhabited.default_of struct_Entry`: the
struct's `has_default` instance is field-wise defaults, which is what the CLR produces, and
the type parameters it needs are added to the method's defaulted ones.

**R33.20. Loops in `[Open]` methods frame what they do not assign.** R33.15's frame now
follows calls: a call `this.M(...)` of an `[Open]` method with a body assigns what `M`
assigns, transitively; any other call on the receiver may assign anything. A loop over the
open receiver names the record before it (`with before. assert (B.pts_to this before)`) and
adds to its invariant `this.f == before.f` for each field neither the loop nor its `[Open]`
callees assign, so that the invariant need not restate them. A closed receiver whose record
a loop writes is named the same way when the loop calls a method on it; a loop with no such
call states what it keeps itself (R5.8), and the extra frame facts only burden its proof
(`HashSet.Remove`'s `RemoveWrites` timed out under them).

**R33.21. Switches that end in a non-returning arm.** An `if`/`else` all of whose arms end in
a `return`, a `throw` or a call of a `[DoesNotReturn]` method, at least one in a `return`, is
a returning statement for R5.5b. R5.14's expansion of `TryInsert`'s `switch (behavior)` --
`return true;`, `ThrowDuplicateKey(key); break;`, `return false;` -- is such a chain. A
`Debug.Assert` message may be an interpolated string over enum and primitive locals and
parameters (it is effect-free, and dropped).

**R33.22. A raising call while the receiver is open.** A call of a method that may throw,
made while a non-`[Open]` method holds its receiver opened (R4.10), is bracketed by a
refold before it and an unfold after it: if it throws, the method's `raises` clause needs the
invariant. `Resize(HashHelpers.ExpandPrime(_entries.Length))` is the case. A call with an
object the receiver owns as an argument (`_set.Add(…)` on a `SortedSet` field) is not
bracketed: the open receiver holds that object's permission, and the call's own raising
path closes the receiver (R27.38).

**R33.23. Guards nested in an `if`/`else`.** R24.14's copying of the tail into an `if`'s arms
applies also when the `if` is not a guard chain but holds a `return` somewhere inside it:
`SetAt(int, TKey, TValue)`'s `if (…) { if (Equals(…)) { …; return; } } else { if (…) { …;
return; } }` followed by the rest of the method. Each arm that does not already return gets
the tail, after which every inner `if` is an R5.5b guard with its tail.

**R33.24. A `ref` argument is a write.** R4.11's scan counts a call with a `ref` or `out`
argument rooted at a `ref` local or an instance field as a write: the callee may write
through it, and R33.16 writes the element back. Before this, a method whose only write was
`SetKey(ref s, k)` through `ref Slot s = ref _slots[i]` was classified read-only, and its
contract stated against the unchanged model (unsound).

**R33.25. Constructors of a class that owns arrays.** Four pieces make
`OrderedDictionary`'s constructors translate:
(a) a nullable reference field the constructor does not assign (`_comparer`) starts as
`None`, the value `new` gives it;
(b) a constructor's module opens the modules its class's model and invariant read (its
`[Spec]` helpers), as the class's methods' modules do;
(c) `x ?? d`, where `x` is nullable and `d` is not, has `d`'s (non-nullable) type, and a
value is stored into a nullable field or local as `Some` when its type is the same F* type
as the option's — two spec types are the same when they are bound to the same F* name and
their arguments are the same, element-wise (`EqualityComparer<T>` and
`IEqualityComparer<T>` both bind to `Equality.comparer`);
(d) `x == d` and `x != d` (R20.9) where one side is an option and the other a value compare
the option with `Some d`; and a constructor that builds an object owning arrays joins the
record it writes as R33.15's `[Open]` methods do.

**R33.26. Borrowing members that read through a local, and auto-properties.** R28.2's
`var d = _dictionary;` aliases the borrowed object only if the local is never written. A
write *through* a reference-typed local — `ref d._entries[i]`, `d._a[i] = …` — writes the
heap, not the local, so R4.11's never-written check stops at a member or element access on a
reference: `ref Entry entry = ref d._entries[_index];` leaves `d` an alias. An instance
auto-property of a borrowing struct (`Current { get; private set; }`) is its backing field
(R3.4), so a member body reads and assigns it as a field of `self`, and an assignment to it
makes the member a writer of the struct (R28.2's `ref self`). `OrderedDictionary.Enumerator`
is the case.

**R33.27. A window of the receiver's array.** `ReadOnlySpan<T> s = _a.AsSpan(0, _n);` in a
method that opens its receiver (R4.10) borrows the field's array at the receiver's
permission (R17.5 at the fraction R3.10c gives the receiver). While the span is live, a loop
carries the span (an ordinary local) instead of the array, and the borrow's receipt is
framed around it. A window still borrowed when the method returns -- the usual case when a
loop returns from inside it, where C# has no place for `Pal.Restore` -- is restored before
the receiver is closed, latest first; an array-range window is first collapsed by
`splice_same`, so that a window left unwritten gives back the array exactly as it was
(which a read-only receiver's refold at its model needs). `Pal.Contents` of `.AsSpan`'s
window is otherwise R17.8's. The borrow's source and bounds are field accesses for R4.10c,
so a method whose only field access is a span's initializer opens its receiver.
`PriorityQueue.FindIndex` is the case.

**R33.28. Writing the fields of a fresh object of the class.** R27.44 opens another object
of the method's class around a read of its field. A statement that *writes* one -- an
assignment to `o.f`, to `o.a[i]`, or an array copy into `o.a` -- with `o` a local or
parameter held whole by its invariant (a class without regions) is bracketed the same way,
but the bracket closes at the model of what the statement left (R4.11a's witness), not the
one it opened at: so each such statement must leave the class invariant true, as a public
method's exit must. A loop that writes `o`'s fields changes `o`'s model, which it then
quantifies. A local has no model named on entry, so a read's bracket names the one its
invariant holds. `List.GetRange`/`ConvertAll` (`list._items`, `list._size` of the list they
allocate) are the case.

### Findings (§33)

* **Soundness (fixed, R33.6).** `x is null` on an array was translated as `false`, and
  `x is not null` as `true`. `OrderedDictionary.Clear`'s `if (_buckets is null)` and
  `IndexOf`'s `if (_buckets is not null)` were translated as constants.
* `HashHelpers.ExpandPrime` throws `ArgumentException` once `oldSize` reaches
  `MaxPrimeArrayLength`.
* `SetAt(int, TKey, TValue)` compares `Equals(key, e.Key)`, while `IndexOf` compares
  `Equals(entry.Key, key)`: the two orders agree only for a symmetric comparer, which the
  contract of `IEqualityComparer<T>` does not require.
* The public `IndexOf(TKey)` passes one local, `_`, by `ref` to both of the private
  `IndexOf`'s out-parameters; harmless only because that callee never reads them (R33.7).
* There is no key distinctness for `OrderedDictionary` (or `Dictionary`, `HashSet`) without
  a symmetric, transitive comparer: `TryInsert` refuses a key `k` when `Equals(e.Key, k)` for
  some stored `e`, so two stored keys may still be "equal" under the other argument order.
  The model therefore states no distinctness; `IndexOf` promises *a* matching index.
* (R33.13) An annotated expression-bodied indexer was silently not translated, and an
  expression-bodied constructor's body was dropped.
* **Soundness (fixed, R33.24).** A write through a `ref` argument rooted at a `ref` local
  into a field's array was not counted by R4.11, so such a method was read-only.
* `TryInsert` with `OverwriteExisting` on an existing key replaces the value without
  incrementing `_version`, as does `SetAt(int, TValue)`, so an enumerator in progress does
  not fail on a value change (as `Dictionary`'s does not). The contracts say nothing about
  `_version`, so this is consistent; it is recorded because the indexer's setter is a
  mutation that enumerators tolerate.
* `Resize` holds a `Debug.Assert` that the new size is at least `_count`; every caller
  establishes it (`ExpandPrime`'s result exceeds a full table's length; `EnsureCapacity` and
  `TrimExcess` pass `GetPrime` of a bound at least `_count`), and `Resize`'s precondition
  says so.
* `HashHelpers.GetPrime(min)` throws on a negative `min` and otherwise returns at least
  `min`; `ExpandPrime(oldSize)` throws exactly when `oldSize >= MaxPrimeArrayLength` (for
  non-negative `oldSize`). The trusted `GetPrime` contract and `ExpandPrime`'s verified one
  state these normal-return facts, which `TryInsert`'s growth needs.
* The harness does not define `SYSTEM_COLLECTIONS`, so the string-comparer special cases
  (`NonRandomizedStringEqualityComparer`, `RehashIfNecessary`'s randomized rehash and
  `Resize`'s `forceNewHashCodes` block) are excluded by the preprocessor and not verified.
* `PriorityQueue.Remove` sifts from an arbitrary index, so it inherits §26's
  `(index << 2) + 1` wrap: its contract requires `Count <= 2^29`, like `Dequeue`'s.
  With a null comparer, `FindIndex` compares with `EqualityComparer<TElement>.Default`
  on the generic path; its contract uses one predicate, `ElemEq`, for both paths, so it
  promises the first index matching under the comparer in use, and `Remove`'s
  "non-deterministic" remark is, for a given heap layout, deterministic.
* `List.ConvertAll`, `GetRange` and `Slice` write the fresh list's `_items` and `_size`
  directly, bypassing the constructor's checks; the verified contracts confirm that the
  `List` invariant (`_size <= _items.Length`) holds afterwards (R33.28).

### Trusted (§33)

* `Pulse.Lib.CSharp.Platform.intptr_size`: an unspecified `int` (`IntPtr.Size`), bound by
  `pal/OrderedDictionary/Support.cs`.
* `pal/OrderedDictionary/HashHelpers.cs` replaces two of `HashHelpers`' bodies:
  `GetPrime` (a prime at least `min`, at most `MaxPrimeArrayLength` when `min` is) by a
  search with the same contract but not the BCL's prime table, and `FastMod` (Lemire's
  multiply-shift remainder) by `value % divisor`, which the BCL asserts it equals for a
  divisor at most `int.MaxValue`. `ExpandPrime` and `GetFastModMultiplier` are the real
  bodies, verified.
* System.Collections' `ThrowHelper.ThrowKeyNotFound`, `ThrowDuplicateKey`,
  `ThrowConcurrentOperation`, `ThrowIndexArgumentOutOfRange` and `ThrowVersionCheckFailed`
  carry `[Throws]` and `[Ensures("false")]`; their bodies (a `throw`) are translated and
  checked against these contracts.
