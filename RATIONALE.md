# Why are the languages of the subterms added together?

The alternative would be to have *equivalent* languages in the subterms,
as is done in most effect systems.
However, consider indexed languages, or rather, language with state.
A language with state may be used for ensuring that some node is not nested more
than X times.
Two subterms may have different states.
You could imagine a primitive to unify them, but it seems complicated.
Another solution is to make state explicit, have a language define its type-level state.
This is also complicated.

# Why is # linear variables tracked in the tag?

Because if it were only tracked in the language, we can not know
whether other languages bind any linear variables.
We could predicate that there must only be one linear variable binding language,
but that would require knowing all the languages used and complicates languages
hidden beneath over languages.
Tracking the number of linear variables in the tag cleanly solves this.

# Why can there only be one tag? What if it were extensible?

This is somewhat equivalent to making language state first-class and
requiring that a language appear at most once.
You run into the issue that you need to know whether a language has already
been used.

# Why are languages not polymorphic in Term?

You can do this but I haven't thought of a use-case.
If there is one it makes sense.
