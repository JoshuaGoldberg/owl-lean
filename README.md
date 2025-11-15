# OwlLean
A type checker for Owl, implemented in Lean 4

Supports most of the current features, including :
- Labels
- Types
- Terms
- Label based information flow
- Subtyping for types and type variables
- Corruption sets for labels
- Security Lattice representations
- And more ...

Additionally, we have included extra features for a more streamlined typechkick experience :
- Annotations for terms
- Non-recursive Lambdas and let bindings
- Specific notation for if statement typechecking
- And more here as well ...

## Owl Lore

Owl posed us with some unique challenges when trying to design a valid typechecker.
The baseline idea was to implement the set of typing rules and judgements within Owl,
and then define a function that took in a term and a type, and output a proof that the term
indeed typechecked with that type, utilizing the previously defined typing judgements to construct said proof. 
As a visualization, we could imagine a small judgement :
```
____________
True ⊢ Bool  
```
We could then define a mock example of our desired function as follows
``` lean
inductive has_type : tm -> ty -> Prop where
| T_True : has_type .True Bool

def typecheck (e : tm) (t : ty) : Option (has_type e t) :=
match e with
| .True =>
  has_type.T_True
| _ => .none
```
Then, we could call ``(typecheck True Bool)`` and get a valid proof in return that tells us what we want to know. Returning a proof is nice, as we can at least be assured that what we've done is valid, and since Lean lets us seamlessly integrate proofs as return types,
we get a pretty nice and clean result.

Sadly, Owl does not play nicely purely under these assumptions for a few reasons. Instead, we are forced to improvise, adapt, and write up some arguably cursed code to compensate.

## Issue 1 -  Ambiguous typing rules

The first hurdle on the path to realizing an Owl typechecker is the issue of knowing which types to apply in certain rules. An example of this is the typing judgement for the fixlam (recursive lambda) case:

Insert here

The issue with this rule is the existence of ``t1``, as it does not exist within the original type, but is instead selected and used within the rule. This is great for the theory, but when trying to typecheck, it's very annoying to not know the type of ``t1``, 
as otherwise we'd need to somehow guess the proper type such that we could typecheck the body. Therefore, we need to have some way of knowing what types are available without needing to guess. The easy solution would simply be to require that everything is typed within the term itself, changing the form of ``fixlam fun x => true`` to ``fixlam (fun : Any -> True) x => true``. This could work, but it puts a lot of burden on the user to annotate every single term they use, which makes using the typechecker pretty cumbersome since there is a decent variety of terms available in the language. Thankfully, more solutions exist to our predicament, and we found it in the form of bidirectional typing. In essence, we can split our traditional ``has_type`` check into ``check`` and ``synthesize``. In more detail, ``check`` does the traditional form of typechecking that we would expect, while ``synthesize`` attempts to infer the type of a term without supplying an actual type to check against. 

This solves the issue we have with fixlam (mostly), as we can now synthesize a type for the body, and let that resulting type be what we use for ``t1``. We do have to be careful when implenting things in this way, but we can at least rely on the fact that we're returning proofs once again. This means that both ``check`` and ``synthesize`` need to return proofs, with checks returning a proof that a term has a type, with synthesization returning a pair of a type, and a proof that a term has that synthesized type. To ensure the user doesn't have to worry about when to use ``check`` or ``synthesize``, we we implement both cases for every term, and use the correct version when necessary. 

With this, we can now keep fixlam in the form ``fixlam fun x => body``, and the results will play nicely with each other, since every term can now be synthesized and checked!

## Issue 2 -  Not every term can be synthesized

Alright, that last point was a lie. *Ideally* every term could be synthesized, but this is not an ideal world (note that if every term could be synthesized, we could also eliminate checking terms all together). In many cases, this is not an issue, as we choose when to check and when to synthesize in our definition. However, synthesizing is needed in cases like the aforementioned body of a fixlam, since we do not know the type otherwise. We can now touch upon another feature of Owl, which are the ``inl`` and ``inr`` terms, which are used to deal with ``sum`` types, as seen here:

Insert here

It would be easy to typecheck this case normally, as the provided type includes more than what is checked within the term. But when synthesizing, we need to generate the type itself. All we can do is generate the left or right side of the ``sum`` type, but not both. This makes synthesizing impossible in this case, as we have no good way of filling in the missing side of the type without guessing or a default case. The result is that if the body of a fixlam is ``inl`` or ``inr``, synthesization will fail, along with the typecheck, even if the term is properly typed within the typing judgements. 

So, what do we do? We could step back and simply force users to supply both types within the terms, converting ``inl e`` into ``inl e : (t1 + t2)``. But as mentioned before, this puts more burden on the user. Additionally, there are plenty of cases where this extra information would be useless, as it is not needed when a check is performed over synthesis. On top of all this, it would make designing the language tedious, as we would need to integrate into current and potentially future terms the exact information needed to make synthesis work.

Instead, we opt for a more general solution. The introduction of a ``annot`` term, that allows the user to selectivley annotate a term with a type when needed. The logic for this is actually specified within the bidirectional typing paper too, as a way to force synthesis when a term can only be checked. The typing rule is:

Insert here

What this means is that if a term can be checked, then by checking the term against the supplied type, we can synthesize the result and return it. 

With this, we can now annotate the type of ``inl`` and ``inr`` by wrapping them in the annotation type, such as ``((inl *) : (Unit + Bool))``, and this will properly synthesize. It also means we can simply use ``(inl *)`` when synthesis is not needed. With both bidirectional typing in the form of ``check`` and ``synthesis``, alongside a defined annotation term, we no longer need to worry about terms not carrying enough information about types to properly formulate a proof. 

## The Elephant in the room

With the above modifcations, we have been able to expand the typechecker design to handle a large variety of cases in terms. In fact, the majority of terms in Owl can likely now be typechecked without worry, as long as we're careful to implemnt proper proof constructions for checks and synthesis. Thankfully, we can again rely on the fact that it is proofs being returned, meaning that they are valid conclusions assuming the definition has no errors. That being said, these issues are not the main issue when it comes to designing a proper typechecker. We can now shift our focus to aspects of the language that are more specific to Owl itself, as well as the unique challenges those features present to our current typechecking model.

## Issue 3 - Subtyping

A core part of Owl's design is the inclusion of subtyping, written ``t1 <: t2``, meaning that ``t1`` is a subtype of ``t2``. This pops up in various rules within the language, such as with type lambdas:

Insert here

Additionally, Owl allows for the following rule: 

Insert here

Which allows a for a term to have type ``t2`` if it has a ``t1`` and ``t1`` subtypes  ``t2``. This allows us to write some more creative definitions, such as the following:

Insert here

Which is allowed as all terms are a subtype of ``Any``. This means, of course, that we need to add subtyping to our typechecker design, otherwise we lose out on a lot of expressibility with what we can write. Doing this is actually pretty straightforward, as we can mostly focus on extending our typechcker with this new feature. We did this by adding an additional
definition, called ``subtype``, that takes in two types (``t1`` and ``t2``), and returns a proof that ``t1 <: t2`` if possible.  

## Issue 4 - Labels and Constraints

Constraints play a big role in working with the language of Owl. In short, a constraint defines the relation between two labels. To keep it simple, we can assume most constraints take the form of ``l1 ⊑ l2``, meaning that ``l1`` flows to ``l2``.  

## Issue 5 - Corruption Sets
