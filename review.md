# Brian Nugent's review-1 of the GV formalization

**Reviewer:** Brian Nugent (https://github.com/brian-nugent).
**Window:** 2026-04-08 → 2026-04-15 (the "lull" between proving phase and the
Codex refactor / compress era).
**Subject:** the sorry-free `wip/grothendieck-vanishing` branch as of 2026-04-07.
**Status:** review-1 of two. Review-2 is in progress as of 2026-05-01.

This file is the primary source. Direct quotes from this review are cited
throughout `TECHNICAL_REPORT_GV.md` §5 and §6.4.

---

Large change: The overall file structure needs to be refactored. There are files with indescriptive names like Auxiliary.lean, Setup.lean and SetupCore.lean. There are also files that are incorrectly labeled like ClosedOpenDecomposition.lean. There are also a lot of results in the wrong file. Some files should be combined, there only needs to be one file on flasque sheaves. Other files should be split, FiniteGeneratorReduction.lean should be split so there is a file on general colimits of sheaves and another file for the noetherian case. Its ok to have some big files and some small files, the important thing is that the file names are descriptive so its easy to search through. After this refactor, documentation should be added at the top of every file explaining what is done in that file as well as what the main definitions/theorems are in that file.

Large change: Many lemmas/theorems are stated for (F : TopCat.Sheaf AddCommGrpCat.{u} X) but then the theorem proves something for either F.val or (sheafToPresheaf _ _).obj F (sometimes for morphisms between sheaves as well). This is unidiomatic. The correct way of doing this is to state the results for {F : Presheaf AddCommGrpCat X} (hF : IsSheaf F) instead. This can easily be applied for (F : TopCat.Sheaf AddCommGrpCat.{u} X) but is better. There are many results across the files that are done this way so this will require a large refactor. Note there are still SOME results that should be stated in terms of (F : TopCat.Sheaf AddCommGrpCat.{u} X).

Large change: There are results proven with the assumptions {G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)} (ip : InjectivePresentation G) that only refer to ip.shortComplex in the theorem statement. These should all be generalized to work for {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} instead. If the assumption that the middle term is injective is necessary for a particular theorem then it can be added as an additional assumption [S.X₂.Injective].

Large change: Provide API for sheaf cohomology. Currently, anytime it needs something proven about H, it proves it for Ext then uses the fact that H is defined in terms of Ext. This is messy, it is better to have a separate file proving all results it needs about H (in this file it is ok to prove them for Ext then use that) then in all other files, only refer to these API lemmas. That way the definition of H never needs to be unfolded in terms of Ext (except in the one file providing the API).

Large change: sheafH_preserves_filtered_colimits and PushforwardHVanishing both prove "if A=0 then B=0" when they should really be proving that "A is isomorphic to B". In both cases, the proofs are essentially the same (maybe with a slightly harder diagram chase, the four lemmas are probably helpful) and the more general result is significantly more useful.

Auxiliary.lean
General: There shouldn't be a file named Auxiliary, its not descriptive. Almost all the results in this file are about topological krull dimension so it should be labeled as such. It should realize when writing the lemmas of this file that the reason it has to is because there is no API for topological krull dimension in mathlib. Instead of proving a bunch of random specific lemmas, it should add API.
18: This is a special case of CategoryTheory.Limits.IsZero.epi
28: This is TopCat.Sheaf.isTerminalOfEqEmpty
33-63: It has uncovered a genuine gap in mathlib API concerning irreducible spaces of dimension 0.
68: Should prove any non-empty topological space has nonnegative krull dimension.
74: Doesn't need to be its own theorem
84: This is useful
105: After writing (Order.height s : WithBot ℕ∞) so many times its clear we should define TopologicalSpace.IrreducibleCloseds.height the same way Ideal.height is defined.
65-153: This whole section is a bunch of ad hoc lemmas that it needed because there is very little API for topological krull dimension in Mathlib. It should refactor this by working out what key facts are needed and would be useful in the future, then derive its special cases from those. Basically, it should add API, not just prove exactly what it needs.
156: Doesn't need to be its own theorem
163: I think this is fine

ClosedImmersion.lean
General: The proof of TopCat.closedIncl_counit_isIso is horrendous. It should be able to notice proofs like these and see that they are unacceptable and need to be simplified.
29: This is a useful definition. API should be built for it and can be modeled after that of TopologicalSpace.Opens.inclusion'. It should probably be defined in the TopologicalSpace.Closeds namespace.
32: This follows from TopCat.Presheaf.app_injective_iff_stalkFunctor_map_injective and CategoryTheory.Sheaf.isLocallyInjective_iff_injective.
32-290: All of these results hold for sheaves over more general categories. Exactly which assumptions are needed on the category for each result should be worked out and the lemmas should be proven in a more general form.
55: This is TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso but maybe that isn't in this version of mathlib?
70: This is proving the compatibility of some maps but in a very specific case and in an extremely unidiomatic way. Taking a closed subset s and then taking an element (x : TopCat.of s) is ridiculous.
104: It is proving that for a sheaf on a closed subset, the counit of the pushforward pullback adjunction is an isomorphism. This is equivalent to proving that the pushforward functor is fully faithful which would be the idiomatic way of proving this. Instead it spends 150 lines doing an inefficient calculation on stalks.
256: This is CategoryTheory.isIso_comp_right_iff
261: This is CategoryTheory.isIso_comp_left_iff
267: Proving compatibilities like this are useful but it should not be only for AddCommGrpCat.
290: This is useful and is decently written.

ZeroOutside.lean
General: Most of this is copied from my PR so its not too bad.
13-22: These should not be in the ZeroOutside file.
16/22: These should not be in the Sheaf namespace.
102-114: These lemmas should not exist at all and really should not be in the Presheaf namespace.
36-220: This is all pretty much directly copied from my PR yet somehow it made a lot of the proofs longer and less idiomatic. Why didn't it just copy it directly?
227: This is pretty well written, it should probably be a def instead of an abbrev with API built for it.
234: If the proof is just "inferInstance" you don't need to prove it. Just infer it when it is needed.

ZeroOutsideFinset.lean
General: It makes a bunch of abbrevs for everything it wants to be able to talk about. Instead, it should make one or two key definitions in the correct generality and work with those. In this case, defining the subsheaf generated by a collection of sections is useful but creating new definitions to work with finset is useless and sloppy.
23: This does not need to be its own definition.
28: This is just familyGeneratorMap for a finset.
36: This does not need to be its own definition and it shouldn't be just for finsets either.
43: If the proof is just "inferInstance" you don't need to prove it. Just infer it when it is needed.
53: This does not need to be its own definition.
59: This proof is ok

FlasqueVanishing.lean
General: FlasqueVanishing is not in this file, rename it. This is the first file where it works with cohomology and it is already clear that there is missing API for sheaf cohomology. Rather than building it, the AI seems perfectly happy to just unfold the definition and work with Ext the whole time. This is not the correct approach, instead it should make notes of exactly which properties of H it needs and what general facts about H implies them. Then, the general facts can be proven and the specific properties can be inlined. The definition of freeAbSheaf in this file is good and it even proved a useful API lemma freeAbSheafHomEquiv_naturality. freeAbSheaf is mathematically equivalent to zeroOutsideInt which is defined in a different file. Since freeAbSheaf is marked as private I imagine zeroOutsideInt is the one that gets used elsewhere. There should be a refactor to replace freeAbSheaf with zeroOutsideInt or vice versa. Both should be tried and then evaluated to see which works better.
50-52: I'm not convinced this is true. Try deleting this and test the compile time difference.
70: Seems like you could use that the forgetful functor from sheaves to presheaves reflects limits/colimits to make this cleaner.
76: Should just use that additive functors take 0 to 0. This requires the construction of a functor version of H.
111: Doesn't need to be its own lemma.
117: Doesn't need to be its own lemma. Can be simplified to ShortComplex.ShortExact.mk (ShortComplex.exact_cokernel f)
61-134: This whole section seems to be proving some very basic properties of stalks in a very roundabout way. It should think about what the best generalization is that easily gives these results. Maybe just that the stalk functor is exact?
145: This should be a class so it can be inferred.
151: This is just CategoryTheory.sheafSections.
156: This should be replaced with an instance showing that it is Additive.
220-356: This is a zorn's lemma argument that is pretty technical and ugly. It is done much better in my PR, it should just copy it.
383-421: This is a good start, it is defining something and actually providing some useful API to work with it. To test, it should look through all the times these definitions are used in the proofs and make sure that it is not simply unfolding the definition. Properties of these that it needs should be given in API lemmas.
435: This is actually quite good. It gets around using ZeroOutside (a very ugly construction) by using the yoneda presheaf. This is much cleaner and uses existing things in mathlib so its a win win.
442: And we're right back to useless lemmas…
455: Probably doesn't need to be its own lemma and can be baked into the proof of flasque vanishing instead.

FlasqueCohomology.lean
General: Line 51 is the first (I expect there to be many) result being proven for the short exact sequence coming from an injective presentation. There should be no lemmas proven with these assumptions. Instead, they should be proven for {S : ShortComplex (TopCat.Sheaf AddCommGrpCat X)} (hS : S.shortExact) and if it is really necessary, [S.X₂.Injective]. Then they can easily be applied to the injective presentation case but are more useful in general. The theorems proving Subsingleton of something should probably be instances and the assumptions for many of the lemmas should also have Subsingleton be inferred. If designed correctly, this makes it easier to use.
18: This can be written as a single term. The two refines and exact approach is unidiomatic.
42: This is just Equiv.subsingleton.symm
51: Lemmas like these are too specific. This should be replaced with more general API for doing diagram chasing for sheaf cohomology along with the fact that cohomology vanishes for injective objects.
93: Why isn't the assumption in the theorem IsFlasqueSheaf F? Instead it writes out the definition of IsFlasqueSheaf.

SetupCore.lean
General: This file should be split up and given more descriptive names. SetupCore, Setup and Auxiliary are all not descriptive enough. Many of the theorems in this file are private but there's no reason for this. Many of them are even useful theorems so they definitely should not be private.
20: This definition is incredibly unnatural, why does it depend of X at all?
34/45: These should probably infer the Subsingleton instances.
58: This is good.
143: This should not be its own lemma. Also it is probably easier to use the fact that A morphism in AddCommGrpCat is surjective if and only if it is an Epi then use general left/right cancelation results for isomorphisms.
162/166: I'm not convinced these actually save time, try building the project without them and see what the difference is.
171-229: These are both a very special case of the fact that pushforward for a closed immersion is exact. This should be proven then all these special cases will follow easily. You already get for free that pushforward preserves finite limits (since it is an adjoint) so you only need to show that it preserves finite colimits. This is probably easiest to do using CategoryTheory.Functor.preservesFiniteColimits_tfae, which will require essentially exactly the proof you have in closedIncl_pushforward_epi_g but will be a much more useful result.
233: All the results you prove for sheaf cohomology end up just defeq abusing the fact that it is defined using Ext. You should instead provide enough API for H that you don't need to keep unfolding its definition.
336: Pushforward along a closed immersion preserves cohomology all together (up to isomorphism)! You should prove this more general fact (i.e. provide this isomorphism). This can be done using the same argument, take an injective presentation, use that flasque pushes forward to flasque, etc.
376: Having "let" lines inside a theorem statement is extremely odd.
380: Isn't i just closedIncl which you defined earlier?
423: This is a very unnatural statement. Instead, you should just define the short exact sequence you are referring to and prove some API for it. Then you can just use that sequence instead of applying this weird lemma.

ReducibleVanishing.lean
General: This file does not need to exist. Just put this wherever it is used. Also, the comment says "(re-exported by Setup.lean as ReducibleVanishing)" but this is not actually in Setup.lean. Plus, why would you prove the same thing twice and call them ReducibleVanishing' and ReducibleVanishing?

Setup.lean
General: This file contains a single random lemma. This should probably go in the same file as all the other topologicalKrullDim results. Or if that creates an import cycle, change the name of this file at the very least.

PresheafFilteredColimit.lean
General: It likes writing out ConcreteCategory.hom but this can usually be left out and the coercion will take care of it. The code in this section is especially hard to read. Some of this is because it is technical in nature but most of it can be done much better. Many of these results are essentially about colimits in a functor category, since presheaves are defined as a functor category. The AI does not seem to recognize this and proves many result specifically for presheaves on a topological space that already exist in mathlib more generally. In fact, many of these results are instead proven for sheafToPresheaf.obj F where F is a sheaf which is even more specific than proving them for presheaves. For the results that actually require F to be a sheaf, they should be done with the assumptions {F : Presheaf AddCommGrpCat X} (hF : IsSheaf F) rather than starting with a sheaf and applying the forgetful functor. Line 80 is an especially egregious example. This file should be entirely rewritten with this in mind.
20: The documentation does not appear to correctly reflect what is actually being proven here. It seems to claim that this is about presheaves but it is actually about sheaves that are then forgotten down to the category of presheaves.
20: Doesn't this just follow from morphisms taking 0 to 0?
74: Why do we need the cover to be finite here. Does this need to be its own lemma?
86: I cannot work out what is being proven here. Improve the documentation for this theorem.
121: This statement is written decently aside from the presheaf issue discussed in the General section and the fact that J' probably does not need to be small. The proof should be golfed down substantially. It is currently almost 300 lines of code and I can't imagine it needs to be more than 100. Some of the lines are clearly useless, I deleted 187, 191 and 266 and it compiled fine.
411: This is good.

ConstantSheafFlasque.lean
General: This file proves that the constant presheaf associated to Z on an irreducible topological space is flasque. First of all, this is true for any constant presheaf (there's nothing special about Z) so it should be proven in more generality. Second, it never uses IsFlasqueSheaf which it defined in an earlier file and just writes out Epi (...) each time. The proofs in this file are a bit cleaner than in others but the theorem statements are very hard to parse.
11: No need to make this definition specifically for Z.
15: This abbrev doesn't need to exist.
18: This should probably be replaced with a more general fact saying that a sheaf evaluated at the empty set is zero (i.e. a subsingleton group).

ClosedOpenDecomposition.lean
General: This file is incorrectly named. In this file is the reduction of the proof down to the irreducible case. This doesn't need to be its own file and these two theorems should just go before the proof of the main theorem in GrothendieckVanishing.lean.

DimZeroVanishing.lean
General: Another short file. These two theorems should also go in GrothendieckVanishing.lean. The documentation at the top of this file is good and should be done for every file.

FiniteGeneratorReduction.lean
General: Another bad file name. The contents of this file should be put in files that reflect what they are about. The flasque results should go in the flasque file, the results about filtered colimits should go in a file about filtered colimits of sheaves (maybe just rename this file), etc.
33: I looked up Gabriel's theorem and this does not appear to be it.
38: This is good that you prove this for ANY colimit and not just THE colimit.
74/82: These definitions are really specific. All of these should probably be done for sheaves over a concrete category with some added assumptions.
109: This is good.
68-170: Putting aside the fact that it could be more general, this is a good proof that a sheaf is the colimit of its finitely generated subsheaves.
193: It shouldn't need to proof this aux theorem. It can just state the theorem the correct way (which it does in line 380) then use "induction n generalizing…". This has the effect it wants of putting variables into the induction hypothesis.
193: This is another example where instead of proving "A=B", it proves "if A is zero then B is zero".
193: This is a huge proof that should be cleaned up but the general strategy looks good to me.
393: This is not currently being used for anything, although it can hopefully be used to show the more general result that cohomology commutes with filtered colimits on Noetherian spaces (this result is claimed numerous times in the documentation but never actually proven.)
515: This is good.
534/537: These abbrevs put us many layers deep in AI generated definitions, it should think about how to make all its definitions better. As a human trying to verify what it is writing, the hardest part is when there are multi layer definitions like this.

SheafStalkAlgebra.lean
23: It is weird to have these statements that have the inductive hypothesis baked in. It would be better to just have a lemma proving zeroOutsideInt T has vanishing cohomology (or just prove it is flasque) then this theorem can be inlined when you need it.
49/82: You might as well just prove these are isos right? In fact, there's no need to restrict to zeroOutsideInt, these maps should be isos on stalks for any sheaf.
107: Seems like you want that the stalk functor is exact here.
150: The assumption that the krull dimension of X is > 0 is not needed. It is only used to show the krull dimension is not ⊥ but this follows from the fact that X is nonempty (which is included in the irreducible assumption. There should be an API lemma proven saying that the krull dimension of X is bot if and only if X is empty. Make sure this is proven in the appropriate generality!

StalkGeneratorAlgebra.lean
General: This should be combined with SheafStalkAlgebra.lean. Then it should think about which results will be useful in the future and which results could be useful in a more general form. From there, it should make a plan about how to clean these results up so the file is not just 500 lines of hyperspecific lemmas. Lemmas that are only used once can be inlined and the whole file should be golfed down substantially.
20/35: These are good.
41: This is pretty weird and specific.
60: This is basically just TopCat.Presheaf.mono_of_stalk_mono and doesn't need to be its own lemma.
73: Is this useful for anything?
86/135: Aren't these the same theorem? There should only be one.
155: This is just Int.subgroup_cyclic but for Ulift Z and can probably be deduced from it. The way this is stated looks ridiculous.
191: Surely there's a way to state 155 and 191 in a more idiomatic way. Maybe something about the subgroup generated by the element?

IrreducibleStep.lean
General: This file contains some of the more technical steps in the proof. It requires some tricky stalk calculations to show that any subsheaf of the sheaf Z_U contains a subsheaf isomorphic to Z_V. At the moment, I cannot think of any more general results that this would follow from so the AI's current strategy of just "hacking away" until it proves it is fine. This file should be golfed down significantly but besides that its fine. The results of this file have very few implicit or inferred variables. This would make them very annoying for a human to use as each input would have to be put in manually.
274/298/321: These should not need the hpos assumption.

GrothendieckVanishing.lean
General: Why is grothendieck_vanishing_aux needed with this explicit induction hypothesis? Why can't we just do induction on n in the proof of GrothendieckVanishing?
